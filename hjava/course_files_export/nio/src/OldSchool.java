import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

public class OldSchool {
    public static void main(String[] args) {
        File file = new File("abc.txt");
        byte[] wholeContent = new byte[(int)file.length()];
        byte[] buffer = new byte[3];
        try(FileInputStream fis = new FileInputStream(file)) {
            int readCount = -1;
            int contentPointer = 0;
            while((readCount = fis.read(buffer)) != -1) {
                String s = new String(buffer);
                System.out.println(s);
                for(int i=0; i<readCount; ++i) {
                    wholeContent[contentPointer++] = buffer[i];
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
