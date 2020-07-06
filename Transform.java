package ie.tcd.netlab.objecttracker.helpers;

import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.Matrix;
import android.graphics.ImageFormat;
import android.media.Image;
import android.graphics.YuvImage;
import android.graphics.Rect;
import android.media.JetPlayer;
import android.support.annotation.NonNull;
import android.util.Log;
import java.io.InputStream;
import java.io.BufferedInputStream;
import android.graphics.ImageFormat;
import android.graphics.Bitmap.CompressFormat;
import org.json.JSONObject;

import java.io.FileOutputStream;
import java.nio.ByteBuffer;
import java.io.ByteArrayOutputStream;

import ie.tcd.netlab.objecttracker.testing.Logger;

public class Transform {

    /**
     * Returns a transformation matrix from one reference frame into another.
     * Handles cropping (if maintaining aspect ratio is desired) and rotation.
     *
     * @param srcWidth Width of source frame.
     * @param srcHeight Height of source frame.
     * @param dstWidth Width of destination frame.
     * @param dstHeight Height of destination frame.
     * @param applyRotation Amount of rotation to apply from one frame to another.
     *  Must be a multiple of 90.
     * @param maintainAspectRatio If true, will ensure that scaling in x and y remains constant,
     * cropping the image if necessary.
     * @return The transformation fulfilling the desired requirements.
     */
    public static Matrix getTransformationMatrix(
            final int srcWidth,
            final int srcHeight,
            final int dstWidth,
            final int dstHeight,
            final int applyRotation,
            final boolean maintainAspectRatio) {
        final Matrix matrix = new Matrix();

        if (applyRotation != 0) {
            // Translate so center of image is at origin.
            matrix.postTranslate(-srcWidth / 2.0f, -srcHeight / 2.0f);

            // Rotate around origin.
            matrix.postRotate((float) applyRotation);
        }

        // Account for the already applied rotation, if any, and then determine how
        // much scaling is needed for each axis.
        final boolean transpose = (Math.abs(applyRotation) + 90) % 180 == 0;

        final int inWidth = transpose ? srcHeight : srcWidth;
        final int inHeight = transpose ? srcWidth : srcHeight;

        // Apply scaling if necessary.
        if (inWidth != dstWidth || inHeight != dstHeight) {
            final float scaleFactorX = dstWidth / (float) inWidth;
            final float scaleFactorY = dstHeight / (float) inHeight;

            if (maintainAspectRatio) {
                // Scale by minimum factor so that dst is filled completely while
                // maintaining the aspect ratio. Some image may fall off the edge.
                final float scaleFactor = Math.max(scaleFactorX, scaleFactorY);
                matrix.postScale(scaleFactor, scaleFactor);
            } else {
                // Scale exactly to fill dst from src.
                matrix.postScale(scaleFactorX, scaleFactorY);
            }
        }

        if (applyRotation != 0) {
            // Translate back from origin centered reference to destination frame.
            matrix.postTranslate(dstWidth / 2.0f, dstHeight / 2.0f);
        }

        return matrix;
    }

    public static @NonNull byte[] yuvBytes(Image img) {

        Image.Plane Y = img.getPlanes()[0]; // luminance
        Image.Plane VU = img.getPlanes()[2];  // interleaved V and U samples, needed for NV21
        //Image.Plane UV = img.getPlanes()[1];  // interleaved U and V samples, I think

        // the interleaving of V and U samples is hardware dependent, all that's guaranteed
        // is that plane 1 contains U samples and plane 2 V samples.  if they are interleaved
        // then the stride will be 2, so we can use that as a sanity check
        if (VU.getPixelStride()!=2) {
            Logger.addln("\nWARN Possible YUV format problem in Transform.yuvBytes()");
        }

        int Yb = Y.getBuffer().remaining();
        int VUb = VU.getBuffer().remaining();
        byte[] data = new byte[Yb + VUb + 1]; // VUb is on byte short, will cause overflow when rotate
        // no easy way to avoid the following memcpy even though its expensive.  the
        // planes in the Image object are hardware generated byte buffers, but we can't
        // be sure that they are contiguous (if they were we could just use JNI to
        // get a pointer to the start of plane[0] and define a byte buffer that spans
        // plane[0] and plane[1] i.e effectively a cast via JNI)
        Y.getBuffer().get(data, 0, Yb);
        VU.getBuffer().get(data, Yb, VUb);
        return data;
    }

     /*public static @NonNull byte[] imagetoyuvRot(Image img, int rotation, int jpegQuality) {
         // returns byte array corresponding to YUV planes of img after rotation

         Logger.tick("yuvtoJPG1");
         byte[] data = yuvBytes(img);

         int w = img.getWidth(), h=img.getHeight();
         int ww=w, hh=h;
         switch (rotation) {
             case 0:
                 break;
             case 90:
                 ww = h;
                 hh = w;
                 data = rotateYUV420Degree90(data, w, h);
                 break;
             case 180:
                 data = rotateYUV420Degree180(data, w, h);
                 break;
             case 270:
             case -90:
                 ww = h;
                 hh = w;
                 data = rotateYUV420Degree270(data, w, h);
                 break;
             default:
                 Logger.addln("\nWARN yuvRotToJPEG() invalid rotation: " + rotation);
         }
         Logger.add("(1: "+Logger.tock("yuvtoJPG1") +" (rot:"+rotation+")");
         return YUVtoJPEG(data,ww,hh,jpegQuality);
      }*/

    public static byte[] YUVtoJPEG(byte[] yuv, int ww, int hh, int jpegQuality) {


        // compress yuv byte array to jpeg
        final YuvImage yuvImage = new YuvImage(yuv, ImageFormat.NV21, ww, hh,null);
        ByteArrayOutputStream outStream=new ByteArrayOutputStream();

        yuvImage.compressToJpeg(new Rect(0, 0, ww, hh), jpegQuality, outStream);
        // yuvImage uses libjpeg (turbo?) for compression and seems pretty fast, see here:
        // https://android.googlesource.com/platform/frameworks/base.git/+/android-4.3_r2/core/jni/android/graphics/YuvToJpegEncoder.cpp
        return outStream.toByteArray();
    }




    public static byte[] convertRGBtoYUV(Bitmap b) {

        int width=b.getWidth(), height=b.getHeight();

        int [] argb = new int[width*height];
        b.getPixels(argb, 0, width, 0, 0, width, height);

        width = (width/2)*2; height=(height/2)*2; // snap toyuv even size (needed for some coco images)

        final int frameSize = width * height;
        int yIndex = 0;
        int uvIndex = frameSize;
        byte[] yuv420sp=new byte[width*height*3/2];

        int R, G, B, Y, U, V;
        int index = 0;
        for (int j = 0; j < height; j++) {
            for (int i = 0; i < width; i++) {

                R = (argb[index] & 0xff0000) >> 16;
                G = (argb[index] & 0xff00) >> 8;
                B = (argb[index] & 0xff);

                // well known RGB to YUV algorithm
                Y = ((66 * R + 129 * G + 25 * B + 128) >> 8) + 16;
                U = ((-38 * R - 74 * G + 112 * B + 128) >> 8) + 128;
                V = ((112 * R - 94 * G - 18 * B + 128) >> 8) + 128;

                // NV21 has a plane of Y and interleaved planes of VU each sampled by a factor of 2
                //    meaning for every 4 Y pixels there are 1 V and 1 U.  Note the sampling is every other
                //    pixel AND every other scanline.
                yuv420sp[yIndex++] = (byte) ((Y < 0) ? 0 : ((Y > 255) ? 255 : Y));
                if (j % 2 == 0 && index % 2 == 0) {
                    yuv420sp[uvIndex++] = (byte) ((V < 0) ? 0 : ((V > 255) ? 255 : V));
                    yuv420sp[uvIndex++] = (byte) ((U < 0) ? 0 : ((U > 255) ? 255 : U));
                }
                index++;
            }
        }
        return yuv420sp;
    }

    /************************************************************************************/
    private static byte[] rotateYUV420Degree90(byte[] data, int imageWidth, int imageHeight) {
        byte[] yuv = new byte[imageWidth * imageHeight * 3 / 2];
        // Rotate the Y luma
        int i = 0;
        for (int x = 0; x < imageWidth; x++) {
            for (int y = imageHeight - 1; y >= 0; y--) {
                yuv[i] = data[y * imageWidth + x];
                i++;
            }
        }
        // Rotate the U and V color components
        i = imageWidth * imageHeight * 3 / 2 - 1;
        for (int x = imageWidth - 1; x >= 0; x = x - 2) {
            for (int y = 0; y < imageHeight / 2; y++) {
                yuv[i] = data[(imageWidth * imageHeight) + (y * imageWidth) + x];
                i--;
                yuv[i] = data[(imageWidth * imageHeight) + (y * imageWidth)
                        + (x - 1)];
                i--;
            }
        }
        return yuv;
    }

    private static byte[] rotateYUV420Degree180(byte[] data, int imageWidth, int imageHeight) {
        byte[] yuv = new byte[imageWidth * imageHeight * 3 / 2];
        int i;
        int count = 0;
        for (i = imageWidth * imageHeight - 1; i >= 0; i--) {
            yuv[count] = data[i];
            count++;
        }
        for (i = imageWidth * imageHeight * 3 / 2 - 1; i >= imageWidth
                * imageHeight; i -= 2) {
            yuv[count++] = data[i - 1];
            yuv[count++] = data[i];
        }
        return yuv;
    }
    public static byte[] rotateYUV420Degree180p(byte[] data, int imageWidth, int imageHeight) {
        byte[] yuv = new byte[imageWidth * imageHeight * 3 / 2];
        int i;
        int count = 0;
        for (i = imageWidth * imageHeight - 1; i >= 0; i--) {
            yuv[count] = data[i];
            count++;
        }
        for (i = imageWidth * imageHeight * 3 / 2 - 1; i >= imageWidth
                * imageHeight; i -= 2) {
            yuv[count++] = data[i - 1];
            yuv[count++] = data[i];
        }
        return yuv;
    }

    private static byte[] rotateYUV420Degree270(byte[] data, int imageWidth,
                                                int imageHeight) {
        return rotateYUV420Degree180(rotateYUV420Degree90(data, imageWidth, imageHeight),
                imageWidth, imageHeight);
    }

    /************************************************************************************/
    private static void fillBytes(final Image.Plane[] planes, final byte[][] yuvBytes) {
        // Because of the variable row stride it's not possible to know in
        // advance the actual necessary dimensions of the yuv planes.
        for (int i = 0; i < planes.length; ++i) {
            final ByteBuffer buffer = planes[i].getBuffer();
            if (yuvBytes[i] == null) {
                yuvBytes[i] = new byte[buffer.capacity()];
            }
            buffer.get(yuvBytes[i]);
        }
    }

    // The following are from the tensorflow demo ImageUtils.  Should replace
    // with jni implemenations though as these are surely slow !

    // This value is 2 ^ 18 - 1, and is used to clamp the RGB values before their ranges
    // are normalized to eight bits.
    private static final int kMaxChannelValue = 262143;

    private static int YUV2RGB(int y, int u, int v) {
        // Adjust and check YUV values
        y = (y - 16) < 0 ? 0 : (y - 16);
        u -= 128;
        v -= 128;

        // This is the floating point equivalent. We do the conversion in integer
        // because some Android devices do not have floating point in hardware.
        // nR = (int)(1.164 * nY + 2.018 * nU);
        // nG = (int)(1.164 * nY - 0.813 * nV - 0.391 * nU);
        // nB = (int)(1.164 * nY + 1.596 * nV);
        int y1192 = 1192 * y;
        int r = (y1192 + 1634 * v);
        int g = (y1192 - 833 * v - 400 * u);
        int b = (y1192 + 2066 * u);

        // Clipping RGB values to be inside boundaries [ 0 , kMaxChannelValue ]
        r = r > kMaxChannelValue ? kMaxChannelValue : (r < 0 ? 0 : r);
        g = g > kMaxChannelValue ? kMaxChannelValue : (g < 0 ? 0 : g);
        b = b > kMaxChannelValue ? kMaxChannelValue : (b < 0 ? 0 : b);

        return 0xff000000 | ((r << 6) & 0xff0000) | ((g >> 2) & 0xff00) | ((b >> 10) & 0xff);
    }

    private static void convertYUV420ToARGB8888(
            byte[] yData, byte[] uData, byte[] vData,
            int width, int height,
            int yRowStride, int uvRowStride, int uvPixelStride,
            int[] out) {

        int yp = 0;
        for (int j = 0; j < height; j++) {
            int pY = yRowStride * j;
            int pUV = uvRowStride * (j >> 1);

            for (int i = 0; i < width; i++) {
                int uv_offset = pUV + (i >> 1) * uvPixelStride;

                out[yp++] = YUV2RGB(
                        0xff & yData[pY + i],
                        0xff & uData[uv_offset],
                        0xff & vData[uv_offset]);
            }
        }
    }


//    public static Bitmap imageToBitmap(Image image) {
//
//        assert (image.getFormat() == ImageFormat.NV21);
//
//        // NV21 is a plane of 8 bit Y values followed by interleaved  Cb Cr
//        ByteBuffer ib = ByteBuffer.allocate(image.getHeight() * image.getWidth() * 2);
//
//        ByteBuffer y = image.getPlanes()[0].getBuffer();
//        ByteBuffer cr = image.getPlanes()[1].getBuffer();
//        ByteBuffer cb = image.getPlanes()[2].getBuffer();
//        ib.put(y);
//        ib.put(cb);
//        ib.put(cr);
//
//        YuvImage yuvImage = new YuvImage(ib.array(),
//                ImageFormat.NV21, image.getWidth(), image.getHeight(), null);
//
//        ByteArrayOutputStream out = new ByteArrayOutputStream();
//        yuvImage.compressToJpeg(new Rect(0, 0,
//                image.getWidth(), image.getHeight()), 50, out);
//        byte[] imageBytes = out.toByteArray();
//        Bitmap bm = BitmapFactory.decodeByteArray(imageBytes, 0, imageBytes.length);
//        Bitmap bitmap = bm;
//
//        // On android the camera rotation and the screen rotation
//        // are off by 90 degrees, so if you are capturing an image
//        // in "portrait" orientation, you'll need to rotate the image.
//        return bitmap;
//    }

    public static Bitmap convertYUVtoRGB(Image image) {
        int image_w=image.getWidth(), image_h=image.getHeight();

        Logger.tick("bytes");
        final Image.Plane[] planes = image.getPlanes();
        byte[][] yuvBytes = new byte[3][];
        fillBytes(planes, yuvBytes);
        int yRowStride = planes[0].getRowStride();
        final int uvRowStride = planes[1].getRowStride();
        final int uvPixelStride = planes[1].getPixelStride();
        Logger.add(" (b: "+Logger.tock("bytes"));

        Logger.tick("c");
        int[] rgbBytes = new int[image_w * image_w];
        convertYUV420ToARGB8888(
                yuvBytes[0], yuvBytes[1], yuvBytes[2],
                image_w, image_h,
                yRowStride, uvRowStride, uvPixelStride,
                rgbBytes);
        Logger.add(" c: "+Logger.tock("c"));

        Logger.tick("bm");
        Bitmap rgbFrameBitmap = Bitmap.createBitmap(image_w, image_h, Bitmap.Config.ARGB_8888);
        rgbFrameBitmap.setPixels(rgbBytes, 0, image_w, 0, 0, image_w, image_h); //convert to RGB
        Logger.add(" bm: "+Logger.tock("bm")+")");

        return rgbFrameBitmap;

        /*
        // ---------------------------------------------------------
        // renderscipt yuv->rgb, untested but seems fast
        Logger.tick("r");
        RenderScript  mRS  = RenderScript.create(context);
        ScriptIntrinsicYuvToRGB yuvToRgbIntrinsic
                = ScriptIntrinsicYuvToRGB.create(mRS, Element.RGBA_8888(mRS));;

        Type.Builder tb = new Type.Builder(mRS,
                Element.createPixel(mRS, Element.DataType.UNSIGNED_8, Element.DataKind.PIXEL_YUV));
        tb.setX(image_w);
        tb.setY(image_h);
        tb.setMipmaps(false);
        tb.setYuvFormat(ImageFormat.YUV_420_888);
        Allocation ain = Allocation.createTyped(mRS, tb.create(), Allocation.USAGE_SCRIPT);
        ain.copyFrom(yuvBytes[0]);

        Type.Builder tb2 = new Type.Builder(mRS, Element.RGBA_8888(mRS));
        tb2.setX(image_w);
        tb2.setY(image_h);
        tb2.setMipmaps(false);
        Allocation aOut = Allocation.createTyped(mRS, tb2.create(), Allocation.USAGE_SCRIPT);

        yuvToRgbIntrinsic.setInput(ain);
        yuvToRgbIntrinsic.forEach(aOut);

        Bitmap bitmap = Bitmap.createBitmap(image_w, image_h, Bitmap.Config.ARGB_8888);
        aOut.copyTo(bitmap);
        Logger.add(" r: "+Logger.tock("r")+")");

        return bitmap;*/

    }
    //Source https://stackoverflow.com/questions/44022062/converting-yuv-420-888-to-jpeg-and-saving-file-results-distorted-image
    public static byte[] NV21toJPEG(byte[] nv21, int width, int height, int quality) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        YuvImage yuv = new YuvImage(nv21, ImageFormat.NV21, width, height, null);
        yuv.compressToJpeg(new Rect(0, 0, width, height), 100, out);
        return out.toByteArray();
    }

    public static byte[] YUV420toNV21(Image image) {
        Rect crop = image.getCropRect();
        int format = image.getFormat();
        int width = crop.width();
        int height = crop.height();
        Image.Plane[] planes = image.getPlanes();
        byte[] data = new byte[width * height * ImageFormat.getBitsPerPixel(format) / 8];
        byte[] rowData = new byte[planes[0].getRowStride()];

        int channelOffset = 0;
        int outputStride = 1;
        for (int i = 0; i < planes.length; i++) {
            switch (i) {
                case 0:
                    channelOffset = 0;
                    outputStride = 1;
                    break;
                case 1:
                    channelOffset = width * height + 1;
                    outputStride = 2;
                    break;
                case 2:
                    channelOffset = width * height;
                    outputStride = 2;
                    break;
            }

            ByteBuffer buffer = planes[i].getBuffer();
            int rowStride = planes[i].getRowStride();
            int pixelStride = planes[i].getPixelStride();

            int shift = (i == 0) ? 0 : 1;
            int w = width >> shift;
            int h = height >> shift;
            buffer.position(rowStride * (crop.top >> shift) + pixelStride * (crop.left >> shift));
            for (int row = 0; row < h; row++) {
                int length;
                if (pixelStride == 1 && outputStride == 1) {
                    length = w;
                    buffer.get(data, channelOffset, length);
                    channelOffset += length;
                } else {
                    length = (w - 1) * pixelStride + 1;
                    buffer.get(rowData, 0, length);
                    for (int col = 0; col < w; col++) {
                        data[channelOffset] = rowData[col * pixelStride];
                        channelOffset += outputStride;
                    }
                }
                if (row < h - 1) {
                    buffer.position(buffer.position() + rowStride - length);
                }
            }
        }
        return data;
    }
}
