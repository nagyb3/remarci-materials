import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.Optional;
import java.util.stream.Stream;

public class Feladat3 {
    record Coord(int x, int y) {
        public Coord(String line) {
            this(fromLine(line)[0], fromLine(line)[1]);
        }

        public double distance() {
            return Math.sqrt(x * x + y * y);
        }

        private static int[] fromLine(String line) {
            String[] parts = line.split(",");
            return new int[]{Integer.parseInt(parts[0]), Integer.parseInt(parts[1])};
        }
    }
    public static void main(String[] args) throws Exception {
        fromCoords()
                .map(Coord::new)
                .forEach(System.out::println);

        Optional<Coord> min = fromCoords()
                .map(l->new Coord(l))
                .min(Comparator.comparingDouble(c->c.distance()));
        min.ifPresentOrElse(c->System.out.println("min:\t"+c), ()-> System.out.println("there is no minimum"));

        fromCoords()
                .map(l->new Coord(l))
                .max(Comparator.comparingDouble(c->c.distance()))
                .ifPresentOrElse(c->System.out.println("max:\t"+c), ()-> System.out.println("there is no maximum"));

        String message = fromCoords()
                .map(Coord::new)
                .filter(c->isPrime(c.x()) && isPrime(c.y()))
                .findFirst()
                .map(c->"first prime coords: "+c)
                .orElse("there is no prime coords");
        System.out.println(message);

        System.out.println("all primes count: "+
                fromCoords()
                        .map(Coord::new)
                        .filter(c->isPrime(c.x()) && isPrime(c.y()))
                        .count());
        /*
        Optional<Long> olong = Optional.of(1L);
        olong = Optional.empty();
        Long L = 1L;
        olong = Optional.ofNullable(L);

         */
    }

    private static Stream<String> fromCoords() throws Exception {
        return Files.lines(Path.of("coords.txt"));
    }

    private static boolean isPrime(int n) {
        for(int i=2; i<n/2; ++i) {
            if(n%i==0) {
                return false;
            }
        }
        return true;
    }
}
