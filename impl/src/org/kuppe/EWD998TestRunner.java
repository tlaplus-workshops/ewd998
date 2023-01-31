package org.kuppe;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import org.kuppe.EWD998.Pair;

public class EWD998TestRunner {

	private static final int N = 9;
	
	private static final String HOSTNAME = "localhost";
	private static final int BASEPORT = 4223;
	
	public static void main(String[] args) throws Exception {
		final Random rnd = new Random();
		
		while (true) {
			// Test with n \in 1..N nodes.
			final int n = rnd.nextInt(N) + 1;
			
			// Reversed order starting the initiator node last; initiator would fail when
			// the receiver isn't up when the initiator sends out the first message.  The
			// initiator is the last to join and the last to leave the party.
			final ExecutorService executor = Executors.newFixedThreadPool(n);
			for (int i = n - 1; i >= 0; i--) {

				final Map<Integer, Pair> nodes = new HashMap<>(n);
				for (int j = 0; j < n; j++) {
					nodes.put(j, new Pair(HOSTNAME, BASEPORT + j));
				}
				final int myId = i;
				
				// Cannot .get() the task because the runners would run sequentially and each
				// run blocks until termination is detected.
				executor.submit(() -> {
					new EWD998(nodes, myId, myId == 0);
					executor.shutdown();
					return null;
				});
			}
			
			// Wait forever for the executor to terminate.
			executor.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
			
			// Allow the OS to fully close the sockets, ...
			Thread.sleep(500);
		}
	}
}
