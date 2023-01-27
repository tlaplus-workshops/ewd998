package org.kuppe;

import java.util.Random;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

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

				final String[] ewd998Args = new String[n + 1];
				for (int j = 0; j < ewd998Args.length - 1; j++) {
					ewd998Args[j] = String.format("%s:%s", HOSTNAME, BASEPORT + j);
				}
				ewd998Args[ewd998Args.length - 1] = Integer.toString(i);
				
				// Cannot .get() the task because the runners would run sequentially and each
				// run blocks until termination is detected.
				executor.submit(() -> {
					EWD998.main(ewd998Args);
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
