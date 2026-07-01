import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.channels.FileChannel;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;

public class Feladat1 {
    public static void main(String[] args) {
        String fileName = args[0];
        try(FileChannel fc = FileChannel.open(Path.of(fileName), StandardOpenOption.READ)) {
            ByteBuffer buffer = ByteBuffer.allocate(1);
            for(int i=1; i< args.length; i+=2) {
                long pos = Long.parseLong(args[i]);
                byte expected = Byte.parseByte(args[i+1]);
                fc.position(pos);
                if(fc.read(buffer) != -1) {
                    buffer.flip();
                    byte got = buffer.get();
                    if(got != expected) {
                        System.err.println("Error: on position: "+pos+" byte is different; expected: "+expected+"\t got: "+got);
                        System.exit(1);
                    }
                    buffer.flip();
                }
            }
            System.out.println("All bytes matches on all position");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }

    }
}
