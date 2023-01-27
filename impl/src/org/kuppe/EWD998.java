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

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;

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
		final BlockingQueue<JsonObject> inbox = new LinkedBlockingQueue<>();
		
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
			final JsonObject json = new JsonObject();
			json.add("type", new JsonPrimitive("tok"));
			json.add("q", new JsonPrimitive(0));
			json.add("color", new JsonPrimitive(Color.black.toString()));
			inbox.put(json);
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
					final InputStream inputStream = socket.getInputStream();
					final DataInputStream dataInputStream = new DataInputStream(inputStream);
					final String in = dataInputStream.readUTF();
										
					final JsonObject msg = JsonParser.parseString(in).getAsJsonObject();
					
					// Print the raw message.
					System.out.printf("rcv: %s\n", in);
					
					// See EWD998!RecvMsg.
					vc.merge(msg.get("vc").getAsJsonObject());
					
					inbox.add(msg);
					if (msg.get("type").getAsString().equals("trm")) {
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
			final JsonObject msg = inbox.take();

			int tokenQ = 0;
			Color tokenColor = null;
			
			// --------------------------------------------------------------------------------- //

			// InitiateToken and PassToken
			if (msg.get("type").getAsString().equals("tok")) {
				tokenQ = msg.get("q").getAsInt();
				tokenColor = Color.valueOf(msg.get("color").getAsString());

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
			} else if (msg.get("type").getAsString().equals("pl")) {
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
			} else if (msg.get("type").getAsString().equals("trm")) {
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
				Thread.sleep(randomWork.nextInt(100));
				if (randomWork.nextBoolean()) {
					counter++;
					
					// \E rcv \in Node: replaced with probabilistic choice.
					final String receiver = nodes.get(randomWork.nextInt(nodes.size()));
					sendPayload(receiver);
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
						sendTok(nodes.get(nodes.size() - 1), 0, Color.white);		
						color = Color.white;
					} else {
						for (String n : nodes) {
							sendTrm(n);
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
					sendTok(nodes.get(myId - 1), tokenQ + counter, color == Color.black ? Color.black : tokenColor);
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
					final JsonObject json = new JsonObject();
					json.add("type", new JsonPrimitive("tok"));
					json.add("q", new JsonPrimitive(tokenQ));
					json.add("color", new JsonPrimitive(tokenColor.toString()));
					inbox.add(json);
				}
			}
		}
	}

	private void sendPayload(final String receiver) throws Exception {
		final JsonObject result = new JsonObject();
		result.add("rcv", new JsonPrimitive(receiver));
		result.add("type", new JsonPrimitive("pl"));
		sendMsg(result);
	}

	private void sendTok(final String receiver, final int q, final Color color) throws Exception {
		final JsonObject result = new JsonObject();
		result.add("rcv", new JsonPrimitive(receiver));
		result.add("type", new JsonPrimitive("tok"));
		result.add("q", new JsonPrimitive(q));
		result.add("color", new JsonPrimitive(color.toString()));
		sendMsg(result);
	}

	private void sendTrm(final String receiver) throws Exception {
		final JsonObject result = new JsonObject();
		result.add("rcv", new JsonPrimitive(receiver));
		result.add("type", new JsonPrimitive("trm"));
		sendMsg(result);
	}

	// Boilerplate: Sending messages. 
	private void sendMsg(JsonObject json) throws Exception {
		System.out.printf("snd: %s\n", json);
		
		final String[] s = json.get("rcv").getAsString().split(":");
        final Socket socket = new Socket(s[0], Integer.parseInt(s[1]));

        final OutputStream outputStream = socket.getOutputStream();
        final DataOutputStream dataOutputStream = new DataOutputStream(outputStream);

        json.add("vc", vc.tick().toJson());
        
        dataOutputStream.writeUTF(json.toString());
        dataOutputStream.flush();
        dataOutputStream.close();

        socket.close();
	}
}
