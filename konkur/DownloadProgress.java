import java.io.*;
import java.net.*;
import java.nio.file.Paths;
import java.util.concurrent.atomic.AtomicLong;

public class DownloadProgress {
    private static final String FILE_URL = "https://ftp.ek-cer.hu/pub/mirrors/ftp.archlinux.org/iso/2023.09.01/archlinux-bootstrap-2023.09.01-x86_64.tar.gz";
    private static final String SAVE_FILE_PATH = Paths.get(System.getProperty("user.home"), "Downloads", "archlinux-bootstrap-2023.09.01-x86_64.tar.gz").toString();

    private static final AtomicLong downloadedBytes = new AtomicLong(0);

    public static void main(String[] args) {
        DownloadThread downloadThread = new DownloadThread(FILE_URL, SAVE_FILE_PATH, downloadedBytes);
        downloadThread.start();

        long totalSize = getContentLength(FILE_URL);

        while (downloadThread.isAlive()) {
            try {
                Thread.sleep(100);
                double percentageDownloaded = ((double) downloadedBytes.get() / totalSize) * 100;
                System.out.printf("Downloaded: %.2f%%\n", percentageDownloaded);
            } catch (InterruptedException e) {
                System.out.println("Download cancelled");
                downloadThread.interrupt();
            }
        }

        System.out.println("Download completed!");
    }

    private static long getContentLength(String fileURL) {
        try {
            URL url = new URL(fileURL);
            HttpURLConnection httpConn = (HttpURLConnection) url.openConnection();
            long length = httpConn.getContentLengthLong();
            httpConn.disconnect();
            return length;
        } catch (Exception e) {
            System.out.printf("Connection error.%n%s%n", e);
        }
        return -1;
    }

    static class DownloadThread extends Thread {
        private final String fileURL;
        private final String saveFilePath;
        private final AtomicLong downloadedBytes;

        public DownloadThread(String fileURL, String saveFilePath, AtomicLong downloadedBytes) {
            this.fileURL = fileURL;
            this.saveFilePath = saveFilePath;
            this.downloadedBytes = downloadedBytes;
        }

        @Override
        public void run() {
            try {
                URL url = new URL(fileURL);
                HttpURLConnection httpConn = (HttpURLConnection) url.openConnection();
                int responseCode = httpConn.getResponseCode();

                if (responseCode == HttpURLConnection.HTTP_OK) {
                    try (InputStream inputStream = httpConn.getInputStream();
                         FileOutputStream outputStream = new FileOutputStream(saveFilePath)) {

                        int bytesRead;
                        byte[] buffer = new byte[4096];
                        while ((bytesRead = inputStream.read(buffer)) != -1) {
                            outputStream.write(buffer, 0, bytesRead);
                            downloadedBytes.addAndGet(bytesRead);
                        }

                    } catch (IOException e) {
                        System.out.printf("Error during download.%n%s%n", e);
                    }
                } else {
                    System.out.println("Server replied with code: " + responseCode);
                }
                httpConn.disconnect();
            } catch (Exception e) {
                System.out.println("Download cancelled");
            }
        }
    }
}
