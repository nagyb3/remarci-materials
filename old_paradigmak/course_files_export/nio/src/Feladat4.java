import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;

public class Feladat4 {
    public static void main(String[] args) throws Exception {
        try(FileChannel fileChannel = FileChannel.open(Path.of("megfejtendo_uzenet.txt"))) {
            ByteBuffer buffer = ByteBuffer.allocate((int) fileChannel.size());
            Charset.availableCharsets().forEach((String key, Charset charSet) -> {
                System.out.println("checked: "+key);
                buffer.rewind();
                CharBuffer cb = charSet.decode(buffer);
                if(cb.toString().contains("大")) {
                    System.out.println("found: "+key);
                    System.out.println("message: "+cb.toString());
                    System.exit(0);
                } else {
                    System.out.println(cb.toString());
                }
            }) ;
            System.err.println("Not decoded! :(");
        }
    }
}
