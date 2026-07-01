import java.util.stream.IntStream;

public class Feladat4 {
    public static void main(String[] args) {
        IntStream.iterate(1, i->i+1).limit(100).forEach(System.out::println);
        System.out.println(IntStream.range(1, Integer.MAX_VALUE).mapToLong(i->i).sum());
        System.out.println(IntStream.range(1, Integer.MAX_VALUE).parallel().mapToLong(i->i).sum());
    }
}
