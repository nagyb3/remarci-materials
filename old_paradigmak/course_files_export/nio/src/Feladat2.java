import java.io.File;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.CharBuffer;
import java.nio.channels.FileChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;

public class Feladat2 {
    public static void main(String[] args) throws Exception {
        Path zip = Paths.get("fileok.zip");
        try(FileChannel fc = FileChannel.open(zip, StandardOpenOption.READ)) {
            ByteBuffer header = ByteBuffer.allocate(30);
            int readedBytes = -1;
            while ((readedBytes = fc.read(header)) != -1) {
                header.flip();
                header.order(ByteOrder.LITTLE_ENDIAN);
                short fileNameLength = header.getShort(26);
                int compressedSize = header.getInt(18);
                int uncompressedSize = header.getInt(22);
                short compressMethod = header.getShort(8);
                short extraFieldLength = header.getShort(28);
                ByteBuffer fileNameBuffer = ByteBuffer.allocate(fileNameLength);
                fc.read(fileNameBuffer);
                fileNameBuffer.flip();
                CharBuffer fNameCB = StandardCharsets.US_ASCII.decode(fileNameBuffer);
                System.out.println(fNameCB.toString()+"\tsize: "+uncompressedSize+"\t compress method: "+compressMethod);
                if(compressMethod == 0) {
                    ByteBuffer bb = ByteBuffer.allocate(compressedSize);
                    fc.read(bb);
                    bb.flip();
                    Path folder = Path.of("unzipped");
                    if(!Files.exists(folder)) {
                        Files.createDirectory(folder);
                    }
                    Path unzipped = folder.resolve(fNameCB.toString());
                    Files.createFile(unzipped);
                    try(FileChannel out = FileChannel.open(unzipped, StandardOpenOption.CREATE, StandardOpenOption.WRITE)) {
                        out.write(bb);
                    }
                } else {
                    fc.position(fc.position()+compressedSize+extraFieldLength);
                }
            }
        }
    }
}
