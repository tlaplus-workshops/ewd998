package org.kuppe;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;

// https://github.com/tlaplus-workshops/ewd998/blob/main/EWD998.tla
public class EWD998 {

	public static void main(String[] args) throws Exception {
		// foo:4711 bar:1234 frob:4423 1

		// foo bar frob
		final List<String> nodes = Arrays.asList(args).subList(0, args.length - 1);
		// nodes[1] = bar (zero-indexed)
		final int myId = Integer.parseInt(args[args.length - 1]);

		new EWD998(nodes, myId, Integer.parseInt(nodes.get(myId).split(":")[1]), myId == 0);
	}

	private enum Color {
		black,
		white
	}
	
	private final Random randomWork = new Random();
	private final EWD998VectorClock vc;
	
	public EWD998(final List<String> nodes, final int myId, final int port, final boolean isInitiator) throws Exception {
		final BlockingQueue<String> inbox = new LinkedBlockingQueue<>();
		
		/*
			Init ==
			    /\ active \in [Node -> BOOLEAN]
			    /\ pending = [i \in Node |-> 0]
			    /\ color \in [Node -> Color]
			    /\ counter = [i \in Node |-> 0]
			    /\ token = [pos |-> 0, q |-> 0, color |-> "black"]
			    \* The clock variable is not part of EWD998.
			    /\ clock = [n \in Node |-> [m \in Node |-> 0] ]
		 */
		boolean active = true;
		Color color = Color.white;
		int counter = 0;
		if (isInitiator) {
			// /\ token = [pos |-> 0, q |-> 0, color |-> "black"]
			inbox.put("[tok]0,black");
		}
		
		vc = new EWD998VectorClock(myId, nodes.size());

		boolean terminationDetected = false;
		
		// --------------------------------------------------------------------------------- //
		
		// Boilerplate: Network receiver thread (after Init because Init adds an element to inbox).
		final ExecutorService executorService = Executors.newSingleThreadExecutor();
		executorService.submit(() -> {
			try (ServerSocket serverSocket = new ServerSocket(port)) {
				System.out.printf("Node %s listening on %s\n", myId, serverSocket.getLocalSocketAddress());
				while (true) {
					final Socket socket = serverSocket.accept();
					InputStream inputStream = socket.getInputStream();
					DataInputStream dataInputStream = new DataInputStream(inputStream);
					final String in = dataInputStream.readUTF();
										
					// Print the raw message.
					System.out.printf("rcv: %s < %s\n", nodes.get(myId), in);
					
					final String[] msgAndVC = in.split("\\|");
					assert msgAndVC.length == 2;

					// See EWD998!RecvMsg.
					vc.merge(msgAndVC[1]);
					
					final String msg = msgAndVC[0];
					inbox.add(msg);
					if (msg.startsWith("[trm]")) {
						// See note at marker "aklseflha" below.
						dataInputStream.close();
						inputStream.close();
						socket.close();
						// Orderly terminate this executor to not hang indefinitely.
						executorService.shutdown();
						return;
					}
				}
			} catch (IOException e) {
				e.printStackTrace();
			}
		});
		
		// --------------------------------------------------------------------------------- //
		
		while (true) {
			final String msg = inbox.take();

			int tokenQ = 0;
			Color tokenColor = null;
			
			// --------------------------------------------------------------------------------- //

			// InitiateToken and PassToken
			if (msg.startsWith("[tok]")) {
				// "[tok]-42,black"
				final String[] qAndColor = msg.substring(5).split(",");
				tokenQ = Integer.parseInt(qAndColor[0]);
				tokenColor = Color.valueOf(qAndColor[1]);

				if (isInitiator) {
					/*
					InitiateProbe ==
					    /\ token.pos = 0
					    /\ \* previous round inconclusive:
					        \/ token.color = "black"
					        \/ color[0] = "black"
					        \/ counter[0] + token.q > 0
					    /\ ...
					    /\ UNCHANGED <<active, counter, pending>>                

				    terminationDetected ==
						  /\ token.pos = 0
						  /\ token.color = "white"
						  /\ token.q + counter[0] = 0
						  /\ color[0] = "white"
						  /\ ~ active[0]
					 */
					terminationDetected = tokenQ + counter == 0 && color == Color.white && tokenColor == Color.white
							&& !active;
				}
			} else if (msg.startsWith("[pl]")) {
				/*
					RecvMsg(i) ==
					    /\ pending[i] > 0
					    /\ active' = [active EXCEPT ![i] = TRUE]
					    /\ pending' = [pending EXCEPT ![i] = @ - 1]
					    /\ counter' = [counter EXCEPT ![i] = @ - 1]
					    /\ color' = [ color EXCEPT ![i] = "black" ]
					    /\ UNCHANGED <<token>>
 				 */
				active = true;
				counter--;
				color = Color.black;
			} else if (msg.startsWith("[trm]")) {
				// (aklseflha) The termination message "[trm]" is *not* part of EWD998. Here,
				// the initiator sends a trm message to all nodes including itself after
				// detecting termination. A recipient of a trm message closes its server socket
				// and orderly shuts down its executor service. Additionally, the trm message is
				// added to the inbox to cause this thread (main) to also terminate.
				assert !active;
				assert inbox.isEmpty();
				return;
			} else {
				throw new IllegalArgumentException("Unknown message type");
			}
			
			// --------------------------------------------------------------------------------- //
			

			/*
				SendMsg(i) ==
				    /\ active[i]
				    /\ counter' = [counter EXCEPT ![i] = @ + 1]
				    /\ \E recv \in Node:
				            pending' = [pending EXCEPT ![recv] = @ + 1]
				    /\ UNCHANGED <<active, color, token>>
			 */
			if (active) {
				// Simulate some work...
				Thread.sleep(randomWork.nextInt(6000));
				if (randomWork.nextBoolean()) {
					counter++;
					
					// \E rcv \in Node: replaced with probabilistic choice.
					String receiver = nodes.get(randomWork.nextInt(nodes.size()));
					sendMsg(receiver, "[pl]");
				} else {					
					vc.tick();
				}
			}
			
			// --------------------------------------------------------------------------------- //
				
			/*
				Deactivate(i) ==
				    /\ active[i]
				    /\ active' = [active EXCEPT ![i] = FALSE]
				    /\ UNCHANGED <<pending, color, counter, token>>
			 */
			if (active) {
				active = randomWork.nextDouble() < 0.75d;
			}
			
			// --------------------------------------------------------------------------------- //
			
			// InitiateToken and PassToken actions
			// /\ ...
			// /\ token.pos = i
			if (tokenColor != null) {
				if (isInitiator) {
					/*
						InitiateProbe ==
						    /\ ...
						    /\ token' = [ pos |-> N-1, q |-> 0, color |-> "white"]
						    /\ color' = [ color EXCEPT ![0] = "white" ]
						    /\ UNCHANGED <<active, counter, pending>>                
					 */
					if (!terminationDetected) {
						sendMsg(nodes.get(nodes.size() - 1), "[tok]0,white");		
						color = Color.white;
					} else {
						for (String n : nodes) {
							sendMsg(n, "[trm]");
						}
					}
					tokenColor = null;
				} else if (!active) {
					/*
						PassToken(i) ==
						    /\ ~ active[i]
						    /\ token.pos = i
						    /\ token' = [ token EXCEPT !.pos = @ - 1,
						                               !.q   = @ + counter[i],
						                               !.color = IF color[i] = "black" THEN "black" ELSE @ ]
						    /\ color' = [ color EXCEPT ![i] = "white" ]
						    /\ UNCHANGED <<active, pending, counter>>
 					 */
					sendMsg(nodes.get(myId - 1), String.format("[tok]%s,%s", tokenQ + counter,
							color == Color.black ? Color.black : tokenColor));
					color = Color.white;

					tokenColor = null;
				} else {
					// This node owns the token and is active; keep the unchanged token.
					/*
						Deactivate(i) ==
							    /\ ...
							    /\ UNCHANGED <<..., token>>
						SendMsg(i) ==
						    /\ ...
						    /\ UNCHANGED <<..., token>>
						RecvMsg(i) ==
						    /\ ...
						    /\ UNCHANGED <<token>>
				     */
					inbox.add(String.format("[tok]%s,%s", tokenQ, tokenColor));
				}
			}
		}
	}

	// Boilerplate: Sending messages. 
	private void sendMsg(String receiver, String msg) throws Exception {
		System.out.printf("snd: %s < %s\n", receiver, msg);
		
		final String[] s = receiver.split(":");
        final Socket socket = new Socket(s[0], Integer.parseInt(s[1]));

        final OutputStream outputStream = socket.getOutputStream();
        final DataOutputStream dataOutputStream = new DataOutputStream(outputStream);

        msg += "|" + vc.tick().serialize();
        dataOutputStream.writeUTF(msg);
        dataOutputStream.flush();
        dataOutputStream.close();

        socket.close();
	}
}
