import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public class SyncIterationSolution {

    public static void main(String[] args) {
        listIterate(false, false);
        listIterate(true, false);

        listIterate(true, true);
        listIterate(false, true);

        mapIterate(false, false);

        mapIterate(true, false);
        mapIterate(true, true);
        mapIterate(true, true);
    }

    private static final int ELEM_SIZE = 100_000;

    public static void listIterate(boolean syncedList, boolean synchronizeIterate) {
        List<Integer> list = syncedList ? Collections.synchronizedList(new ArrayList<>()) : new ArrayList<>();

        for (int i = 0; i < ELEM_SIZE; i++) {
            list.add(i);
        }

        Thread t1 = new Thread(() -> {
            for (int i = ELEM_SIZE; i < 2 * ELEM_SIZE; i++) {
                list.add(i);
            }
        });

        Thread t2 = new Thread(() -> {
            try {
                if (synchronizeIterate) {
                    syncIterate(list);
                } else {
                    nonSyncIterate(list);
                }
                System.out.printf("SUCCESS: listIterate(syncedList=%b, synchronizeIterate=%b)%n", syncedList, synchronizeIterate);
            } catch (ConcurrentModificationException e) {
                System.err.printf("FAIL: listIterate(syncedList=%b, synchronizeIterate=%b)%n", syncedList, synchronizeIterate);
            }
        });

        t1.start();
        t2.start();

        try {
            t1.join();
            t2.join();
        } catch (InterruptedException ignored) {
        }

        System.out.println(list.size());
    }

    public static void nonSyncIterate(Collection<Integer> ds) {
        Iterator<Integer> iterator = ds.iterator();

        try (var pw = new PrintWriter("out.txt")) {
            while (iterator.hasNext()) {
                pw.println(iterator.next());
            }
        } catch (FileNotFoundException e) {
            throw new RuntimeException(e);
        }
    }

    public static void syncIterate(Collection<Integer> ds) {
        synchronized (ds) {
            nonSyncIterate(ds);
        }
    }

    public static void mapIterate(boolean useConcurrentMap, boolean synchronizeIterate) {
        System.out.println("mapIterate(" + useConcurrentMap + ", " + synchronizeIterate + ")");

        Map<Integer, Integer> map = useConcurrentMap ? new ConcurrentHashMap<>() : Collections.synchronizedMap(new HashMap<>());
        for (int i = 0; i < ELEM_SIZE; i++) {
            map.put(i, i);
        }

        Thread t1 = new Thread(() -> {
            for (int i = ELEM_SIZE; i < 2 * ELEM_SIZE; i++) {
                map.put(i, i);
            }
        });

        Thread t2 = new Thread(() -> {
            try {
                if (synchronizeIterate) {
                    syncIterate(map.keySet());
                } else {
                    nonSyncIterate(map.keySet());
                }
                System.out.printf("SUCCESS: mapIterate(useConcurrentMap=%b, synchronizeIterate=%b)%n", useConcurrentMap, synchronizeIterate);
            } catch (ConcurrentModificationException e) {
                System.err.printf("FAIL: mapIterate(useConcurrentMap=%b, synchronizeIterate=%b)%n", useConcurrentMap, synchronizeIterate);
            }
        });

        t1.start();
        t2.start();

        try {
            t1.join();
            t2.join();
        } catch (InterruptedException ignored) {
        }

        System.out.println(map.size());
    }
}
