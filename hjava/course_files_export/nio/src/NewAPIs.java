import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

public class NewAPIs {
    public static void main(String[] args) throws Exception {
        Path path = Paths.get("abc.txt");
        Files.lines(path).forEach(System.out::println);
        String content = Files.readString(path);
        //byte[] bytes = Files.readAllBytes(path);
        System.out.println(content);
        Files.copy(path, Paths.get("copied.txt"));
    }
}
