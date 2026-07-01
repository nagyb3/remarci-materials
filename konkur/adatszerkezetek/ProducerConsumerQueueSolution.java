import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;

public class ProducerConsumerQueueSolution {

    public static final int CAPACITY = 10;
    private static final BlockingQueue<Integer> queue = new ArrayBlockingQueue<>(CAPACITY);

    private static class Producer implements Runnable {
        @Override
        public void run() {
            for (int i = 0; i < 10_000; ++i) {
                System.out.println("Producing: " + i);
                try {
                    queue.put(i);
                } catch (InterruptedException e) {
                    break;
                }
            }
            System.out.println("Stop producing.");
        }
    }

    private static class Consumer implements Runnable {

        @Override
        public void run() {
            while (true) {
                Integer num;
                try {
                    num = queue.take();
                    System.out.println("Consuming: " + num);
                    Thread.sleep(1);
                } catch (InterruptedException e) {
                    break;
                }
            }
            System.out.println("Stop consuming.");
        }

    }

    private static class Observer implements Runnable {
        @Override
        public void run() {
            while (true) {
                try {
                    Thread.sleep(2);
                } catch (InterruptedException e) {
                    break;
                }
                StringBuilder sb = new StringBuilder("Snapshot: ");
                for (int num : queue) {
                    sb.append(num).append(" ");
                }
                System.out.println(sb);
            }
            System.out.println("Stop observing.");
        }
    }

    public static void main(String[] args) {
        Thread producer = new Thread(new Producer());
        Thread consumer = new Thread(new Consumer());
        Thread observer = new Thread(new Observer());

        producer.start();
        consumer.start();
        observer.start();

        try {
            producer.join();
        } catch (InterruptedException ignored) {}

        observer.interrupt();

        try {
            Thread.sleep(500);
        } catch (InterruptedException ignored) {}

        consumer.interrupt();
    }
}