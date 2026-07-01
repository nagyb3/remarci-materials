import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;

public class NewWave {
    public static void main(String[] args) {
        File file = new File("abc.txt");
        byte[] wholeContent = new byte[(int)file.length()];
        ByteBuffer buffer = ByteBuffer.allocate(3);
        try(FileInputStream fis = new FileInputStream(file)) {
            FileChannel fc = fis.getChannel();
            int readCount = -1;
            int contentPointer = 0;
            while((readCount = fc.read(buffer)) != -1) {
                // IMPORTANT!
                buffer.flip();
                //buffer.rewind();
                String s = new String(buffer.array());
                System.out.println(s);
                for(int i=0; i<readCount; ++i) {
                    wholeContent[contentPointer++] = buffer.get(i);
                }
            }
            System.out.println(new String(wholeContent));
        } catch (FileNotFoundException e) {
            throw new RuntimeException(e);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
