import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

public class ProducerConsumerWaitNotifySolution {

    public static final int CAPACITY = 10;
    private static final List<Integer> queue = new ArrayList<>(CAPACITY);
    private static final AtomicInteger counter = new AtomicInteger();

    private static class Producer implements Runnable {
        @Override
        public void run() {
            for (int i = 0; i < 10_000; ++i) {
                try {
                    synchronized (queue) {
                        while (queue.size() == CAPACITY) {
                            queue.wait();
                        }
                        System.out.println("Producing: " + i);
                        queue.add(i);
                        queue.notifyAll();
                    }
                    counter.incrementAndGet();
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
                    synchronized (queue) {
                        while (queue.isEmpty()) {
                            queue.wait();
                        }
                        num = queue.remove(0);
                        System.out.println("Consuming: " + num);
                        queue.notifyAll();
                    }
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
                synchronized (queue) {
                    for (int num : queue) {
                        sb.append(num).append(" ");
                    }
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
        Thread observer2 = new Thread(() -> {
           while (true) {
               try {
                   Thread.sleep(3);
               } catch (InterruptedException e) {
                   break;
               }
               System.out.println("Produced so far: " + counter.get());
           }
        });
        producer.start();
        consumer.start();
        observer.start();
        observer2.start();

        try {
            producer.join();
        } catch (InterruptedException ignored) {
        }

        observer.interrupt();

        try {
            Thread.sleep(500);
        } catch (InterruptedException ignored) {
        }

        consumer.interrupt();

        observer2.interrupt();
    }
}