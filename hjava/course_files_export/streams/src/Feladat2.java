import java.io.File;
import java.util.Objects;
import java.util.Scanner;
import java.util.stream.Stream;

public class Feladat2 {
    public static void main(String[] args) throws Exception {
        Scanner scanner = new Scanner(new File("input.txt"));
        Stream.generate(()->{
            if(scanner.hasNext()) {
                return scanner.next();
            }
            return null;
        }).takeWhile(Objects::nonNull).forEach(System.out::println);
    }
}
