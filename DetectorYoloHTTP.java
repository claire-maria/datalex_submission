
package ie.tcd.netlab.objecttracker.detectors;

import android.Manifest;
import android.app.Activity;
import android.content.pm.PackageManager;
import android.graphics.ImageFormat;
import android.graphics.Matrix;

import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Random;
import android.support.annotation.NonNull;
import android.support.v4.content.ContextCompat;
import android.support.v4.app.ActivityCompat;
import android.graphics.RectF;
import android.media.Image;
import android.content.Context;
import android.os.Build;
import android.graphics.Paint;

import java.io.ByteArrayOutputStream;
import java.io.FileOutputStream;
import android.graphics.drawable.BitmapDrawable;
import android.graphics.drawable.Drawable;

import android.graphics.Canvas;
import java.util.ArrayList;
import android.graphics.BitmapFactory;
import android.graphics.Bitmap;
import java.io.IOException;
import java.io.File;
import android.os.Environment;
import android.telecom.Connection;
import android.util.Size;
import android.widget.Toast;

import org.json.JSONArray;
import org.json.JSONObject;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.nio.ByteBuffer;
import java.net.Socket;
import java.net.InetAddress;
import java.net.Inet4Address;
import android.util.Log;

import org.opencv.android.Utils;
import org.opencv.core.Point;
import org.opencv.core.Scalar;
import org.opencv.imgproc.Imgproc;
import org.opencv.core.CvType;
import org.opencv.core.Mat;
import org.opencv.core.MatOfPoint2f;
import org.opencv.core.MatOfPoint;

import org.opencv.core.Rect;

import ie.tcd.netlab.objecttracker.R;
import ie.tcd.netlab.objecttracker.helpers.Recognition;
import ie.tcd.netlab.objecttracker.helpers.Transform;
import ie.tcd.netlab.objecttracker.testing.Logger;

public class DetectorYoloHTTP extends Detector {

//    private final int jpegQuality;
    private int comQuality;
    private InetAddress IP;
    ByteBuffer IPbuf;
    private final String server;
    private final int port;
    private final boolean useUDP;
    private int udpsockfd=-1;
    private Socket tcpsock;
    BufferedOutputStream out;
    BufferedReader in;
    boolean executed = false;
    boolean saved = false;
    private final static int LISTSIZE=1000; // if change this then also change value in udp_socket_jni.c
    public static final String TAG = "MyActivity";
    private int outputHeight = 500;
    private int outputWidth= 600;
    private int outputHW= 800;
    private Mat mOutputROI;

    private boolean bpUpdated = false;

    private Mat mRgba;
    private Mat mHSV;
    private Mat mask;

    private int lo = 20;
    private int up = 20;
    ByteBuffer recvbuf, image_bytes, req_buf, first_img_bytes;
    private final static int MSS=1472;          // max UDP payload (assuming 1500B packets)
    private static final boolean DEBUGGING = false;  // generate extra debug output ?
    public static final int REQUEST_WRITE_EXTERNAL = 3;
    ArrayList<ArrayList<Bitmap>> testtttt = new ArrayList<>();
    ArrayList<Bitmap> lessthanthree = new ArrayList<>();
    ArrayList<Bitmap> deletethis = new ArrayList<>();
    ArrayList<Mat> croppedMatObjs = new ArrayList<>();
    ArrayList<Recognition> recArr = new ArrayList<>();
    ArrayList<Bitmap> coco = new ArrayList<>();
    ArrayList<Bitmap> cropped = new ArrayList<>();
    ArrayList<android.graphics.Rect> rectsOrig = new ArrayList<>();
    ArrayList<ArrayList<Bitmap>> toBeSent = new ArrayList<>();
    ArrayList<ArrayList<Bitmap>> combinedCOCO = new ArrayList<>();
    ArrayList<ArrayList<Bitmap>> listOfCMBLists = new ArrayList<>();
    ArrayList<ArrayList<Bitmap>> GETRIDOFTHISAFTER = new ArrayList<>();
    Bitmap combinedBitmaps;
    Bitmap ucandel;
    byte[] combinedByte;
    byte[] cmbJpeg;
    int cmbH, cmbW;
    Rect origCords = new Rect();

    static {
        System.loadLibrary("udpsocket");
    }
    private native int socket(ByteBuffer addr, int port);
    private native void closesocket(int fd);
    private native String sendto(int fd, ByteBuffer sendbuf, int offset, int len, int MSS);
    private native String sendmmsg(int fd, ByteBuffer req, int req_len, ByteBuffer img, int img_len, int MSS);
    private native int recv(int fd, ByteBuffer recvbuf, int len, int MSS);
    private Context context;
    int delete;

    //private native void keepalive();

    public DetectorYoloHTTP(@NonNull Context context, String server, int comQuality, boolean useUDP) {

        String parts[] = server.split(":");
        this.server=parts[0]; this.port=Integer.valueOf(parts[1]); //server details
        this.IP=null; // this will force DNS resolution of server name in background thread below
                      // (since it may take a while and anyway DNS on the UI thread is banned by android).
        this.comQuality = 100;
        this.useUDP = useUDP;
        this.tcpsock = null;
        this.context = context;
        // can't open sockets here as may not yet have internet permission
        // only open them once, so that tcp syn-synack handshake is not repeated for every image
        if (!hasPermission(context)) { // need internet access to use YoloHTTP
            requestPermission((Activity) context);
        }
        // allocate byte buffers used to pass data to jni C
        recvbuf = ByteBuffer.allocateDirect(MSS*LISTSIZE);
        IPbuf = ByteBuffer.allocateDirect(4); // size of an IPv4 address
        image_bytes=ByteBuffer.allocateDirect(MSS*LISTSIZE);
        first_img_bytes = ByteBuffer.allocateDirect(MSS*LISTSIZE);
        req_buf=ByteBuffer.allocateDirect(MSS);

    }

    protected void finalize() {
        if (udpsockfd >0) {
            closesocket(udpsockfd);
        }
        if (this.tcpsock != null) {
            try {
                this.tcpsock.close();
            } catch(Exception e) {
                Logger.addln("\nWARN Problem closing TCP socket ("+e.getMessage()+")");
            }
        }
    }

    public Detections recognizeImage(Image image, int rotation) {

        android.graphics.Rect crop = image.getCropRect();
        int format = image.getFormat();
        delete = crop.width() * crop.height() *  ImageFormat.getBitsPerPixel(format)/8;
        if (image.getFormat() != ImageFormat.YUV_420_888) {
            // unsupported image format
            Logger.addln("\nWARN YoloHTTP.recognizeImage() unsupported image format");
            Log.e("HELP", "WRONG FORMAT");
            return new Detections();
        }
        return recognize(Transform.YUV420toNV21(image), image.getWidth(),image.getHeight(), rotation);
    }

    @Override
    public Detections recognize(byte[] yuv, int image_w, int image_h, int rotation) {

        byte[] by = Transform.NV21toJPEG(yuv, image_w, image_h, 100);
        Bitmap origialBitmap = BitmapFactory.decodeByteArray(by, 0, by.length);
        //Load cocoDataset
        int[] drawables = new int[]{R.drawable.coco8, R.drawable.coco4, R.drawable.pic1, R.drawable.pic2, R.drawable.pic3, R.drawable.coco1, R.drawable.coco2, R.drawable.coco3,R.drawable.coco7};

//        , R.drawable.coco1, R.drawable.coco2, R.drawable.coco3,
//                R.drawable.coco_val2014_000000002592,  R.drawable.coco_val2014_000000003703
//        R.drawable.coco_val2014_000000003703, R.drawable.coco_val2014_000000006608,
//                R.drawable.coco_val2014_000000008583, R.drawable.coco_val2014_000000009527, R.drawable.coco_val2014_000000011712, R.drawable.coco4, R.drawable.looknice, R.drawable.coco5, R.drawable.coco6,
//                R.drawable.coco7, R.drawable.coco8
        //Save cocodataset & split images with openCV
        if (!executed) {
            Bitmap b = null;
            for (int i = 0; i < drawables.length; i++) {
                coco.add(saveCoco(drawables[i]));
//                Bitmap bitm = saveCoco(drawables[i]);
//                b = getResizedBitmap(bitm, outputWidth, outputHeight);
//                coco.add(b);

            }
//            for(int j = 0 ; j < coco.size() ; j++){
//                toBeSent.add(objectDetforArrayTST(coco.get(j), outputWidth, outputHeight));

            for(int i = 0 ; i < coco.size() ; i++){
                lessthanthree = objectDetforArrayTST(coco.get(i), outputWidth, outputHeight);
                if(lessthanthree.size() <= 3){
                    combinedCOCO.add(lessthanthree);
                }
            }
            Random rand = new Random();
            int n = rand.nextInt(combinedCOCO.size() -1 );
            toBeSent.add(combinedCOCO.get(n));
            executed = true;
        }

        //Get cropped areas of interest using OpenCV
        cropped = objectDetforCameraImage(origialBitmap, outputWidth, outputHeight);
        Detections detects = new Detections();

        //Add these to the data to be sent
        if (cropped.size() != 0) {
            toBeSent.add(cropped);
            Log.e("tot", "Cam Img Size" + cropped.size());
            //combine bitmaps
            combinedBitmaps = combLists(toBeSent);
            //change back to 900
            combinedBitmaps = getResizedBitmap(combinedBitmaps, 900, 900);
            saveBitmapToExternalStorage(combinedBitmaps);
            //remove image data from to the list to be sent
            toBeSent.remove(cropped);
            combinedByte = bitmapToByteArray(combinedBitmaps);
            byte[] convrgbtoyuv = Transform.convertRGBtoYUV(combinedBitmaps);
            combinedByte = Transform.NV21toJPEG(convrgbtoyuv, combinedBitmaps.getWidth(), combinedBitmaps.getHeight(), comQuality);
           // image_h = 900; image_w = 900;
            Logger.tick("d");
            Logger.tick("yuvtoJPG");
            int isYUV;
            image_bytes.clear();
            try {
                if (comQuality > 0) {
                    // we do rotation server-side, android client too slow (takes around 10ms in both java
                    // and c on Huawei P9, while jpeg compressiovoidn takes around 8ms).
                    try {
                         image_bytes.put(Transform.NV21toJPEG(yuv, image_w, image_h, comQuality));
                      //  image_bytes.put(combinedByte);
                        isYUV = 0;
                    } catch (Exception e) {
                        // most likely encoded image is too big for image_bytes buffer
                        Logger.addln("WARN: Problem encoding jpg: " + e.getMessage());
                        Log.e("Problem", "PROBLEM" + detects.results);
                        return detects; // bail
                    }

                } else {
                    try {
                        // send image uncompressed
                        image_bytes.put(yuv);
                        isYUV = 1;


                    } catch (Exception e) {
                        Logger.addln("WARN: Problem encoding jpg: " + e.getMessage());
                        Log.e("Problem", "PROBLEM" + detects.results);
                        return detects; // bail
                    }
                }
            } catch (Exception e) {
                Logger.add("WARN: COMBINEDBYTE BYTE ARRAY IS NULL");
                return detects;
            }
            detects.addTiming("yuvtoJPG", Logger.tockLong("yuvtoJPG"));
            int dst_w = image_w, dst_h = image_h;
            if ((rotation % 180 == 90) || (rotation % 180 == -90)) {
                dst_w = image_h;
                dst_h = image_w;
            }
            Matrix frameToViewTransform = Transform.getTransformationMatrix(
                    image_w, image_h,
                    dst_w, dst_h,
                    rotation, false);
            // used to map received response rectangles back to handset view
            Matrix viewToFrameTransform = new Matrix();
            frameToViewTransform.invert(viewToFrameTransform);

            if (IP == null) {
                // resolve server name to IP address
                try {
                    InetAddress names[] = InetAddress.getAllByName(server);
                    StringBuilder n = new StringBuilder();
                    for (InetAddress name : names) {
                        n.append(name);
                        if (name instanceof Inet4Address) {
                            IP = name;
                            break;
                        }
                    }
                    Logger.addln("\nResolved server to: " + IP);
                    if (IP == null) {
                        Logger.addln("\nWARN Problem resolving server: " + n);
                        return detects;
                    }

                } catch (IOException e) {
                    Logger.addln("\nWARNProblem resolving server " + server + " :" + e.getMessage());
                    return detects;
                }
            }

            String req = "POST /api/edge_app2?r=" + rotation
                    + "&isYUV=" + isYUV + "&w=" + image_w + "&h=" + image_h
                    + " HTTP/1.1\r\nContent-Length: " + image_bytes.position() + "\r\n\r\n";
            StringBuilder response = new StringBuilder();
            if (useUDP) {
                try {
                    Logger.tick("url2");
                    // open connection (if not already open) and send request+image
                    if (udpsockfd < 0) {
                        // put the server IP address into a byte buffer to make it easy to pass to jni C
                        IPbuf.position(0);
                        IPbuf.put(IP.getAddress());
                        udpsockfd = socket(IPbuf, port);
                        Debug.println("sock_fd=" + udpsockfd);
                    }
                    Debug.println("data len=(" + req.length() + "," + image_bytes.position() + ")");
                    Logger.tick("url2a");
                    // copy request to byte buffer so easy to pass to jni C
                    req_buf.clear();
                    req_buf.put(req.getBytes(), 0, req.length());
                    String str = sendmmsg(udpsockfd, req_buf, req.length(), image_bytes, image_bytes.position(), MSS);
                    Debug.println("s: " + str);
                    //Logger.add("s: "+str);
                    detects.addTiming("url2a", Logger.tockLong("url2a"));
                    detects.addTiming("url2", Logger.tockLong("url2"));
                    int count = 1 + (req.length() + image_bytes.position()) / (MSS - 2);
                    detects.addTiming("pkt count", count * 1000);

                    // read the response ...
                    Logger.tick("url3");
                    // need to receive on same socket as used for sending or firewall blocks reception
                    int resplen = recv(udpsockfd, recvbuf, MSS * LISTSIZE, MSS);
                    if (resplen < 0) {
                        Logger.addln("\nWARN UDP recv error: errno=" + resplen);
                    } else if (resplen == 0) {
                        Logger.addln("\nWARN UDP timeout");
                    } else {
                        response.append(new String(recvbuf.array(), recvbuf.arrayOffset(), resplen));
                    }
                    if (response.length() <= 10) {
                        Debug.println(" received " + response.length());
                    }
                    detects.addTiming("url3", Logger.tockLong("url3"));
                    Logger.addln(detects.client_timings.toString());
                    //String pieces[] = response.split("\n");
                    //response = pieces[pieces.length-1];  // ignore all the headers (shouldn't be any !)
                } catch (Exception e) {
                    Logger.addln("\nWARN Problem with UDP on " + IP + ":" + port + " (" + e.getMessage() + ")");
                }
            } else { // use TCP
                try {
                    // open connection and send request+image
                    Logger.tick("url2");
                    if (tcpsock == null) {
                        tcpsock = new Socket(IP, port);
                        out = new BufferedOutputStream(tcpsock.getOutputStream());
                        in = new BufferedReader(new InputStreamReader(tcpsock.getInputStream()));
                    }
                    try {
                        out.write(req.getBytes());
                        out.write(image_bytes.array(), image_bytes.arrayOffset(), image_bytes.position());
                        out.flush();
                    } catch (IOException ee) {
                        // legacy server closes TCP connection after each response, in which case
                        // we reopen it here.
                        Logger.addln("Retrying TCP: " + ee.getMessage());
                        tcpsock.close();
                        tcpsock = new Socket(IP, port);
                        out = new BufferedOutputStream(tcpsock.getOutputStream());
                        in = new BufferedReader(new InputStreamReader(tcpsock.getInputStream()));
                        out.write(req.getBytes());
                        out.write(image_bytes.array());
                        out.flush();
                    }
                    detects.addTiming("url2", Logger.tockLong("url2"));

                    Logger.tick("url3");
                    // read the response ...
                    // read the headers, we ignore them all !
                    String line;
                    while ((line = in.readLine()) != null) {
                        if (line.length() == 0) break; // end of headers, stop
                    }
                    // now read to end of response
                    response.append(in.readLine());
                    detects.addTiming("url3", Logger.tockLong("url3"));
                } catch (Exception e) {
                    Logger.addln("\nWARN Problem connecting TCP to " + IP + ":" + port + "");
                    try {
                        tcpsock.close();
                    } catch (Exception ee) {
                    }
                    ;
                    tcpsock = null; // reset connection
                }
            }
            if (response.length() == 0 || response.toString().equals("null")) {
                Logger.add(" empty response");
                Logger.add(": " + Logger.tock("d"));
                return detects; // server has dropped connection
            }
            // now parse the response as json ...
            try {
                // testing
                //response = "{"server_timings":{"size":91.2,"r":0.4,"jpg":8.4,"rot":34.1,"yolo":48.3,"tot":0},"results":[{"title":"diningtable","confidence":0.737176,"x":343,"y":415,"w":135,"h":296},{"title":"chair","confidence":0.641756,"x":338,"y":265,"w":75,"h":57},{"title":"chair","confidence":0.565877,"x":442,"y":420,"w":84,"h":421}]}
                //              [{"title":"diningtable","confidence":0.737176,"x":343,"y":415,"w":135,"h":296},{"title":"chair","confidence":0.641756,"x":338,"y":265,"w":75,"h":57},{"title":"chair","confidence":0.565877,"x":442,"y":420,"w":84,"h":421}]
                //              cam: 39 {"yuvtoJPG":8,"url2":15,"url3":128,"d":152}"
                JSONObject json_resp = new JSONObject(response.toString());
                JSONArray json = json_resp.getJSONArray("results");
                int i;
                JSONObject obj;
                for (i = 0; i < json.length(); i++) {
                    obj = json.getJSONObject(i);
                    String title = obj.getString("title");
                    Float confidence = (float) obj.getDouble("confidence");
                    Float x = (float) obj.getInt("x");
                    Float y = (float) obj.getInt("y");
                    Float w = (float) obj.getInt("w");
                    Float h = (float) obj.getInt("h");
                    RectF location = new RectF(
                            Math.max(0, x - w / 2),  // left
                            Math.max(0, y - h / 2),  // top
                            Math.min(dst_w - 1, x + w / 2),  //right
                            Math.min(dst_h - 1, y + h / 2));  // bottom

                   // if(y >= 300 && h >= 300) {
                        viewToFrameTransform.mapRect(location); // map boxes back to original image coords
                        Recognition result = new Recognition(title, confidence, location, new Size(image_w, image_h));
                        detects.results.add(result);
                        String sss = String.valueOf(response);
                        Log.e("RESULTS", sss);
                        detects.server_timings = json_resp.getJSONObject("server_timings");
                  //  }
                }
//                String sss = String.valueOf(response);
//                Log.e("MB", sss);
//                detects.server_timings = json_resp.getJSONObject("server_timings");
            } catch (Exception e) {
                Logger.addln("\nWARN Problem reading JSON:  " + response + " (" + e.getMessage() + ")");
            }
        }
            detects.addTiming("d", Logger.tockLong("d"));
            return detects;
        }


    /***************************************************************************************/
    private boolean hasPermission(Context context) {
        return ContextCompat.checkSelfPermission(context, Manifest.permission.INTERNET)
                == PackageManager.PERMISSION_GRANTED;
     }

    private void requestPermission(final Activity activity) {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            if (ActivityCompat.shouldShowRequestPermissionRationale(activity,Manifest.permission.INTERNET)) {
                // send message to user ...
                activity.runOnUiThread(
                        new Runnable() {
                            @Override
                            public void run() {
                                Toast.makeText(activity,
                                        "Internet permission is required to use YoloHTTP",
                                        Toast.LENGTH_SHORT).show();
                            }
                        });
            }
            ActivityCompat.requestPermissions(activity,new String[]{Manifest.permission.INTERNET},
                    2);
            // will enter onRequestPermissionsResult() callback in class cameraFragment following
            // user response to permissions request (bit messy that its hidden inside that class,
            // should probabyl tidy it up).

        }
    }
    //  SAVE FILE, FOR TESTING USAGE
    //HISTO IS DIFFERENT THRESH VALUES
    //CONTOURS IS DRAWN CONTOURS

    //Testing for two levels of blurred (13,13)(2,2) saved in lookatblurredimage AND (7,7)(0) saved in lookatblurredimages2


    public static void saveBitmapToExternalStorage(Bitmap b){
        try {
            String root = Environment.getExternalStorageDirectory().toString();
            File myDir = new File(root + "/finaltest7");
            myDir.mkdirs();
            Random generator = new Random();
            int n = 10000;
            n = generator.nextInt(n);
            String fname = "Image-"+ n +".jpeg";
            File file = new File (myDir, fname);
            try {
                FileOutputStream outF = new FileOutputStream(file);
                b.compress(Bitmap.CompressFormat.JPEG, 100, outF);
                outF.close();

            } catch (Exception e) {
               Log.e("SV", "NOT SAVED");
            }
        }
            catch (Exception e){
                Log.e("SV", "Nope");
            }
    }


    /***************************************************************************************/
    // debugging
    private static class Debug {
        static void println(String s) {
            if (DEBUGGING) System.out.println("YoloHTTP: "+s);
        }
    }
    private Bitmap saveCoco(int imgID) {
        Drawable drawable = context.getResources().getDrawable(imgID);
        Bitmap bitmap = ((BitmapDrawable) drawable).getBitmap();
        return bitmap;
    }
    public static String convertBytesToHex(byte[] bytes) {
        StringBuilder result = new StringBuilder();
        for (byte temp : bytes) {

            int decimal = (int) temp & 0xff;  // bytes widen to int, need mask, prevent sign extension
            String hex = Integer.toHexString(decimal);
            result.append(hex);

        }
        return result.toString();
    }

    public  Bitmap testTry(Bitmap b1, Bitmap b2){
        Bitmap bigbitmap = null;
        int w = b1.getWidth() + b2.getWidth();
        int h;
        if(b1.getHeight() >= b2.getHeight()){
            h = b1.getHeight();
        }else{
            h = b2.getHeight();
        }
        bigbitmap = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888);
        Canvas newCanvas = new Canvas(bigbitmap);

        newCanvas.drawBitmap(b1, 0, 0, null);
        newCanvas.drawBitmap(b2, 50 + b1.getWidth(), 0, null);
        return bigbitmap;
    }


    public Bitmap combLists(ArrayList<ArrayList<Bitmap>> bitmap){

        int totalBitmaps = 0;
        for(int n = 0 ; n < bitmap.size() ; n++){
            for(int m = 0 ; m < bitmap.get(n).size() ; m++){
                totalBitmaps++;
            }
        }
        int w = outputWidth * totalBitmaps, h = outputHeight * 4;
        Bitmap bigbitmap    = Bitmap.createBitmap(w/4, h, Bitmap.Config.ARGB_8888);
        Canvas bigcanvas    = new Canvas(bigbitmap);
        Paint paint = new Paint();
        int iWidth = 0;
        int iHeight = 0;
        Bitmap bmp;
        for(int i = 0; i < bitmap.size(); i++){
            for(int j = 0; j < bitmap.get(i).size(); j++){
                bmp = bitmap.get(i).get(j);

                if(iWidth +  100 < w/4) {
                    bigcanvas.drawBitmap(bmp,  iWidth , iHeight, paint);
                    iWidth += bmp.getWidth() + 50;
                }
                else {
                    iWidth = 0;
                    bigcanvas.drawBitmap(bmp,  iWidth,  iHeight, paint);
                    iHeight += bmp.getHeight() + 50;
                }
            }

        }

        return bigbitmap;
    }


    public static byte[] bitmapToByteArray(Bitmap bitmap){
        ByteArrayOutputStream stream = new ByteArrayOutputStream();
        bitmap.compress(Bitmap.CompressFormat.PNG, 100, stream);
        byte[] byteArray = stream.toByteArray();
        return byteArray;

    }
    public Bitmap[] splitBitmap(Bitmap picture)
    {
        Bitmap[] imgs = new Bitmap[1];
        imgs[0] = Bitmap.createBitmap(picture, 0, 0, picture.getWidth()/2 , picture.getHeight()/2);
        return imgs;
    }
    private static final char[] HEX_ARRAY = "0123456789ABCDEF".toCharArray();
    public static String bytesToHex(byte[] bytes) {
        char[] hexChars = new char[bytes.length * 2];
        for (int j = 0; j < bytes.length; j++) {
            int v = bytes[j] & 0xFF;
            hexChars[j * 2] = HEX_ARRAY[v >>> 4];
            hexChars[j * 2 + 1] = HEX_ARRAY[v & 0x0F];
        }
        return new String(hexChars);
    }

    public Bitmap getResizedBitmap(Bitmap bm, int newWidth, int newHeight) {
        int width = bm.getWidth();
        int height = bm.getHeight();
        float scaleWidth = ((float) newWidth) / width;
        float scaleHeight = ((float) newHeight) / height;
        // CREATE A MATRIX FOR THE MANIPULATION
        Matrix matrix = new Matrix();
        // RESIZE THE BIT MAP
        matrix.postScale(scaleWidth, scaleHeight);

        // "RECREATE" THE NEW BITMAP
   //     Bitmap resizedBitmap = Bitmap.createScaledBitmap(bm, 640,480, true);
        Bitmap resizedBitmap = Bitmap.createBitmap(
                bm, 0, 0, width, height, matrix, true);
    //    bm.recycle();
        return resizedBitmap;
    }
    public static List<byte[]> byteToPortions(byte[] largeByteArray) {
        // create a list to keep the portions
        List<byte[]> byteArrayPortions = new ArrayList<>();

        // 5mb is about 5.000.000 bytes
        int sizePerPortion = 1_000_000;
        int offset = 0;

        // split the array
        while (offset < largeByteArray.length) {
            // into 5 mb portions
            byte[] portion = Arrays.copyOfRange(largeByteArray, offset, offset + sizePerPortion);

            // update the offset to increment the copied area
            offset += sizePerPortion;

            // add the byte array portions to the list
            byteArrayPortions.add(portion);
        }
        return byteArrayPortions;
    }


public Bitmap objectDet(Bitmap b, int bWid , int bHei){
    Mat srcMat = new Mat (bHei, bWid, CvType.CV_8U, new Scalar(4));
    Mat gray = new Mat (bHei, bWid, CvType.CV_8U, new Scalar(4));
    Mat clone = srcMat.clone();
    Mat result = new Mat (bHei, bWid, CvType.CV_8U, new Scalar(4));

    Utils.bitmapToMat(b,srcMat);
//THIS IS CONTOUR DETECTION
    Imgproc.cvtColor(srcMat, gray, Imgproc.COLOR_RGBA2GRAY);
    Imgproc.GaussianBlur(gray,gray,new org.opencv.core.Size(13,13),2,2);
    Imgproc.threshold(gray, gray, 120, 255,Imgproc.THRESH_BINARY);
    Imgproc.Canny(gray,gray,50,150);
    // apply erosion and dilation
    Imgproc.dilate(gray, gray, Mat.ones(new org.opencv.core.Size(5, 5), CvType.CV_8UC1));
    Imgproc.erode(gray, gray, Mat.ones(new org.opencv.core.Size(5, 5), CvType.CV_8UC1));
//ffind and draw contours
    ArrayList<MatOfPoint> contours = new ArrayList<MatOfPoint>();
    Mat hierarchy = new Mat();
    //find contours:
    Imgproc.findContours(gray, contours, hierarchy, Imgproc.RETR_TREE,Imgproc.CHAIN_APPROX_SIMPLE);


    double contSize = 0;
    MatOfPoint2f  approxCurve = new MatOfPoint2f();

    for(int i = 0 ; i < contours.size() ; i++){
        contSize = Imgproc.contourArea(contours.get(i));
        if(contSize > 4000){
            //Convert contours(i) from MatOfPoint to MatOfPoint2f
            MatOfPoint2f contour2f = new MatOfPoint2f( contours.get(i).toArray() );
            //Processing on mMOP2f1 which is in type MatOfPoint2f
            double approxDistance = Imgproc.arcLength(contour2f, true)*0.02;
            Imgproc.approxPolyDP(contour2f, approxCurve, approxDistance, true);
            //Convert back to MatOfPoint
            MatOfPoint points = new MatOfPoint( approxCurve.toArray() );
            // Get bounding rect of contour
            Rect rect = Imgproc.boundingRect(points);


            // draw enclosing rectangle (all same color, but you could use variable i to make them unique)
          //  Imgproc.rectangle(srcMat,new Point(rect.x,rect.y), new Point(rect.x+rect.width,rect.y+rect.height), new Scalar(0,255,0), 3);
           //Now to crop
            Rect rectCrop = new Rect(rect.x, rect.y , rect.width, rect.height);
            result = srcMat.submat(rectCrop);


            //cropped.add(bmp);

        }
    }


        Bitmap bitmap = Bitmap.createBitmap(result.cols(), result.rows(), Bitmap.Config.ARGB_8888);
        Utils.matToBitmap(result, bitmap);


    return bitmap;
  //  return cropped;
}


    public ArrayList<Bitmap> objectDetforArrayTST(Bitmap b, int bWid , int bHei){
       // b = getResizedBitmap(b, outputWidth, outputHeight);
        ArrayList<Bitmap> DetectionsCropped = new ArrayList<>();
        Mat srcMat = new Mat (bHei, bWid, CvType.CV_8U, new Scalar(4));
        Mat gray = new Mat (bHei, bWid, CvType.CV_8U, new Scalar(4));
        Mat clone = srcMat.clone();

        Mat result = new Mat (bHei, bWid, CvType.CV_8U, new Scalar(4));
        Bitmap bitmap = null;
        int count = 0;
        Utils.bitmapToMat(b,srcMat);
//THIS IS CONTOUR DETECTION
        Imgproc.cvtColor(srcMat, gray, Imgproc.COLOR_RGBA2GRAY);
        Imgproc.GaussianBlur(gray,gray,new org.opencv.core.Size(5,5),1,1);
        //Imgproc.threshold(gray, gray, 120, 255,Imgproc.THRESH_BINARY);
        Imgproc.Canny(gray,gray,50,255);
        // apply erosion and dilation
        Imgproc.dilate(gray, gray, Mat.ones(new org.opencv.core.Size(5, 5), CvType.CV_8UC1));
        Imgproc.erode(gray, gray, Mat.ones(new org.opencv.core.Size(5, 5), CvType.CV_8UC1));
//ffind and draw contours
        ArrayList<MatOfPoint> contours = new ArrayList<MatOfPoint>();
        ArrayList<MatOfPoint> LargestContour = new ArrayList<>();
        Mat hierarchy = new Mat();
        //find contours:
        Imgproc.findContours(gray, contours, hierarchy, Imgproc.RETR_TREE,Imgproc.CHAIN_APPROX_SIMPLE);
        Collections.sort(contours, new Comparator<MatOfPoint>() {
            @Override
            public int compare(MatOfPoint o1, MatOfPoint o2) {
                Rect rect1 = Imgproc.boundingRect(o1);
                Rect rect2 = Imgproc.boundingRect(o2);
                int result = Double.compare(rect1.area(), rect2.area());
                return result;
            }

        });
        int size = contours.size() - 1;
        try {
            LargestContour.add(contours.get(size));
        }
        catch (Exception e){
            Logger.add("No Contours");
            Log.e("Det", "No Contours");
        }
        try {
            LargestContour.add(contours.get(size - 1));
        }
        catch (Exception e){
            Logger.add("Only One Contour");
            Log.e("Det", "One Contours");
        }
        try {
            LargestContour.add(contours.get(size - 2));
            Log.e("Det", "Two Contours");
        }
        catch (Exception e){
            Logger.add("Only 2 Contours");
        }
        MatOfPoint2f approxCurve = new MatOfPoint2f();
        for (int i = 0; i < LargestContour.size(); i++) {

                //Convert contours(i) from MatOfPoint to MatOfPoint2f
            MatOfPoint2f contour2f = new MatOfPoint2f(LargestContour.get(i).toArray());
                //Processing on mMOP2f1 which is in type MatOfPoint2f
            double approxDistance = Imgproc.arcLength(contour2f, true) * 0.02;
            Imgproc.approxPolyDP(contour2f, approxCurve, approxDistance, true);
                //Convert back to MatOfPoint
            MatOfPoint points = new MatOfPoint(approxCurve.toArray());
                // Get bounding rect of contour
            Rect rect = Imgproc.boundingRect(points);

                    //Now to crop
                    //  Imgproc.rectangle(srcMat,new Point(rect.x,rect.y), new Point(rect.x+rect.width,rect.y+rect.height), new Scalar(0,255,0), 3);
            Rect rectCrop = new Rect(rect.x, rect.y, rect.width, rect.height);
            android.graphics.Rect r = new android.graphics.Rect(rectCrop.x, rectCrop.y, rectCrop.width, rectCrop.height);
            rectsOrig.add(r);
            result = srcMat.submat(rectCrop);
            bitmap = Bitmap.createBitmap(result.cols(), result.rows(), Bitmap.Config.ARGB_8888);
            Utils.matToBitmap(result, bitmap);
            bitmap = getResizedBitmap(bitmap, outputWidth, outputHeight);
            DetectionsCropped.add(bitmap);
        }


        Log.e("DetectionsSize", String.valueOf(DetectionsCropped.size()));
        return DetectionsCropped;
        //  return cropped;
    }

    public ArrayList<Bitmap> objectDetforArray(Bitmap b, int bWid , int bHei){

        ArrayList<Bitmap> DetectionsCropped = new ArrayList<>();
        Mat srcMat = new Mat (bHei, bWid, CvType.CV_8U, new Scalar(4));
        Mat gray = new Mat (bHei, bWid, CvType.CV_8U, new Scalar(4));
        Mat clone = srcMat.clone();
        Mat result = new Mat (bHei, bWid, CvType.CV_8U, new Scalar(4));
        int count = 0;
        Utils.bitmapToMat(b,srcMat);
//THIS IS CONTOUR DETECTION
        Imgproc.cvtColor(srcMat, gray, Imgproc.COLOR_RGBA2GRAY);
        Imgproc.GaussianBlur(gray,gray,new org.opencv.core.Size(5,5),2,2);
        //Imgproc.threshold(gray, gray, 120, 255,Imgproc.THRESH_BINARY);
        Imgproc.Canny(gray,gray,50,255);
        // apply erosion and dilation
        Imgproc.dilate(gray, gray, Mat.ones(new org.opencv.core.Size(5, 5), CvType.CV_8UC1));
        Imgproc.erode(gray, gray, Mat.ones(new org.opencv.core.Size(5, 5), CvType.CV_8UC1));
//ffind and draw contours
        ArrayList<MatOfPoint> contours = new ArrayList<MatOfPoint>();
        ArrayList<MatOfPoint> contoursLargest = new ArrayList<>();
        Mat hierarchy = new Mat();
        //find contours:
        Imgproc.findContours(gray, contours, hierarchy, Imgproc.RETR_TREE,Imgproc.CHAIN_APPROX_SIMPLE);
        Collections.sort(contours, new Comparator<MatOfPoint>() {
            @Override
            public int compare(MatOfPoint o1, MatOfPoint o2) {
                Rect rect1 = Imgproc.boundingRect(o1);
                Rect rect2 = Imgproc.boundingRect(o2);
                int result = Double.compare(rect1.area(), rect2.area());
                return result;
            }

        });
        int size = contours.size() - 1;
        try {
            contoursLargest.add(contours.get(size));
        }
        catch (Exception e){
            Logger.add("No Contours");
            Log.e("Det", "No Contours");
        }
//        try {
//            contoursLargest.add(contours.get(size - 1));
//        }
//        catch (Exception e){
//            Logger.add("Only One Contour");
//            Log.e("Det", "One Contours");
//        }
//        try {
//            contoursLargest.add(contours.get(size - 2));
//            Log.e("Det", "Two Contours");
//        }
//        catch (Exception e){
//            Logger.add("Only 2 Contours");
//        }


        double contSize = 0;
        MatOfPoint2f  approxCurve = new MatOfPoint2f();
        for(int i = 0 ; i < contoursLargest.size() ; i++){
            contSize = Imgproc.contourArea(contoursLargest.get(i));
            //Convert contours(i) from MatOfPoint to MatOfPoint2f
            MatOfPoint2f contour2f = new MatOfPoint2f( contoursLargest.get(i).toArray() );
            //Processing on mMOP2f1 which is in type MatOfPoint2f
            double approxDistance = Imgproc.arcLength(contour2f, true)*0.02;
            Imgproc.approxPolyDP(contour2f, approxCurve, approxDistance, true);
            //Convert back to MatOfPoint
            MatOfPoint points = new MatOfPoint( approxCurve.toArray() );
            // Get bounding rect of contour
            Rect rect = Imgproc.boundingRect(points);
            // draw enclosing rectangle (all same color, but you could use variable i to make them unique)
            //  Imgproc.rectangle(srcMat,new Point(rect.x,rect.y), new Point(rect.x+rect.width,rect.y+rect.height), new Scalar(0,255,0), 3);
            //Now to crop
            Rect rectCrop = new Rect(rect.x, rect.y , rect.width, rect.height);
            result = srcMat.submat(rectCrop);
            Bitmap bitmap = Bitmap.createBitmap(result.cols(), result.rows(), Bitmap.Config.ARGB_8888);
            Utils.matToBitmap(result, bitmap);
            bitmap = getResizedBitmap(bitmap, outputWidth, outputHeight);
            DetectionsCropped.add(bitmap);

        }
        Log.e("DetectionsSize", String.valueOf(DetectionsCropped.size()));
        return DetectionsCropped;
        //  return cropped;
    }
    public ArrayList<Bitmap> objectDetforCameraImage(Bitmap b, int bWid , int bHei){
        ArrayList<Bitmap> DetectionsCropped = new ArrayList<>();
        Mat srcMat = new Mat (bHei, bWid, CvType.CV_8UC1, new Scalar(4));
        Mat gray = new Mat (bHei, bWid, CvType.CV_8UC1, new Scalar(4));
        Mat result = new Mat (bHei, bWid, CvType.CV_8U, new Scalar(4));
        Utils.bitmapToMat(b,srcMat);
//THIS IS CONTOUR DETECTION
        Imgproc.cvtColor(srcMat, gray, Imgproc.COLOR_RGBA2GRAY);
        Imgproc.GaussianBlur(gray,gray,new org.opencv.core.Size(5,5),2,2);
        //Imgproc.threshold(gray, gray, 120, 255,Imgproc.THRESH_BINARY);
        Imgproc.Canny(gray,gray,50,150);
        // apply erosion and dilation
        Imgproc.dilate(gray, gray, Mat.ones(new org.opencv.core.Size(5, 5), CvType.CV_8UC1));
        Imgproc.erode(gray, gray, Mat.ones(new org.opencv.core.Size(5, 5), CvType.CV_8UC1));
//ffind and draw contours
        ArrayList<MatOfPoint> contours = new ArrayList<MatOfPoint>();
        ArrayList<MatOfPoint> contoursLargest = new ArrayList<MatOfPoint>();
        Mat hierarchy = new Mat();
        //find contours:
        Imgproc.findContours(gray, contours, hierarchy, Imgproc.RETR_TREE,Imgproc.CHAIN_APPROX_SIMPLE);

        try {
            MatOfPoint2f approxCurve = new MatOfPoint2f();
            for (int i = 0; i < contours.size(); i++) {

                //Convert contours(i) from MatOfPoint to MatOfPoint2f
                MatOfPoint2f contour2f = new MatOfPoint2f(contours.get(i).toArray());
                //Processing on mMOP2f1 which is in type MatOfPoint2f
                double approxDistance = Imgproc.arcLength(contour2f, true) * 0.02;
                Imgproc.approxPolyDP(contour2f, approxCurve, approxDistance, true);
                //Convert back to MatOfPoint
                MatOfPoint points = new MatOfPoint(approxCurve.toArray());
                // Get bounding rect of contour
                Rect rect = Imgproc.boundingRect(points);
                if(rect.area() > 2000) {
                    //Now to crop
                  //  Imgproc.rectangle(srcMat,new Point(rect.x,rect.y), new Point(rect.x+rect.width,rect.y+rect.height), new Scalar(0,255,0), 3);
                    Rect rectCrop = new Rect(rect.x, rect.y, rect.width, rect.height);
                    android.graphics.Rect r = new android.graphics.Rect(rectCrop.x, rectCrop.y, rectCrop.width, rectCrop.height);
                    rectsOrig.add(r);
                    result = srcMat.submat(rectCrop);
                    Bitmap bitmap = Bitmap.createBitmap(result.cols(), result.rows(), Bitmap.Config.ARGB_8888);
                    Utils.matToBitmap(result, bitmap);
                    bitmap = getResizedBitmap(bitmap, outputWidth, outputHeight);
                    DetectionsCropped.add(bitmap);
                }

            }
        }
        catch (Exception e){
            Log.e("Det", "No detections");
            Logger.add("No Detections");
        }
        return DetectionsCropped;
        //  return cropped;
    }
    public static int[] getRandomNums() {
        ArrayList<Integer> list = new ArrayList<Integer>();
        int[] nums = new int[4];
        for (int i = 0; i < 14; i++) {
            list.add(new Integer(i));
        }
        Collections.shuffle(list);
        for (int i = 0; i < nums.length; i++) {
            nums[i] = list.get(i);
        }
        return nums;
    }

    public Bitmap try2(ArrayList<Bitmap> bitmap){
        //TODO ADD B IN RANDOM SPOT

        int w = outputHW * 2, h = outputHW * bitmap.size()/2;
        Bitmap bigbitmap    = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888);
        Canvas bigcanvas    = new Canvas(bigbitmap);

        Paint paint = new Paint();
        int iWidth = 0;
        int iHeight = 0;
        Bitmap bmp;
        for (int i = 0; i < bitmap.size(); i++) {
            bmp = bitmap.get(i);
            bmp = getResizedBitmap(bmp, outputHW, outputHW);
            if(iWidth < 1000) {
                bigcanvas.drawBitmap(bmp, iWidth , iHeight, paint);
                iWidth += bmp.getWidth();

            }
            else {
                iWidth = 0;
                bigcanvas.drawBitmap(bmp, iWidth, iHeight, paint);
                iHeight += bmp.getHeight();
            }
        }
        return bigbitmap;
    }


}


