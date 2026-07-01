import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadLocalRandom;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

public class ReadersWritersSolution2 {
    private static final int NUMBER_OF_PROCESSES = 100;
    private static final int DATABASE_SIZE = 100;
    private static final int WRITER_RATIO = 5;
    private static final int MAX_VALUE = 1000;
    private static final int DELAY = 100;

    private static int[] dataBase = new int[DATABASE_SIZE];

    public static void main(String[] args) throws InterruptedException {
        ExecutorService pool = Executors.newCachedThreadPool();
        ReadWriteLock lock = new ReentrantReadWriteLock();

        for (int i = 0; i < NUMBER_OF_PROCESSES; ++i) {
            pool.submit(() -> {
                ThreadLocalRandom rnd = ThreadLocalRandom.current();
                int index = rnd.nextInt(DATABASE_SIZE);

                if (rnd.nextInt(WRITER_RATIO) == 0) {
                    int value = rnd.nextInt(MAX_VALUE);
                    lock.writeLock().lock();
                    try {
                        sleep(DELAY);
                        dataBase[index] = value;
                    } finally {
                        lock.writeLock().unlock();
                    }
                    System.err.println("Written value " + value + " to index " + index);
                } else {
                    int value;
                    lock.readLock().lock();
                    try {
                        sleep(DELAY);
                        value = dataBase[index];
                    } finally {
                        lock.readLock().unlock();
                    }
                    System.err.println("Read value " + value + " from index " + index);
                }
            });
        }

        pool.shutdown();
        pool.awaitTermination(10, TimeUnit.SECONDS);
    }

    static void sleep(int ms) {
        try {
            Thread.sleep(ms);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }
}