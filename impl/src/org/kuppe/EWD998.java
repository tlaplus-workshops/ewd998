package org.kuppe;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.ConnectException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.HashMap;
import java.util.Map;
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

		// foo:4711 bar:1234 frob:4423
		final Map<Integer, Pair> nodes = new HashMap<>();
		for (int i = 0; i < args.length - 1; i++) {
			String[] s = args[i].split(":");
			nodes.put(i, new Pair(s[0], Integer.parseInt(s[1])));
		}
		
		// nodes[1] = bar (zero-indexed)
		final int myId = Integer.parseInt(args[args.length - 1]);

		new EWD998(nodes, myId, myId == 0);
	}

	private enum Color {
		black,
		white
	}
	
	private final Random randomWork = new Random();
	private final Map<Integer, Pair> nodes;
	private final EWD998VectorClock vc;
	
	public EWD998(final Map<Integer, Pair> nodes, final int myId, final boolean isInitiator) throws Exception {
		final BlockingQueue<JsonObject> inbox = new LinkedBlockingQueue<>();
		
		this.nodes = nodes;
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
			try (ServerSocket serverSocket = new ServerSocket(nodes.get(myId).port)) {
				System.out.printf("Node %s listening on %s\n", myId, serverSocket.getLocalSocketAddress());
				while (true) {
					final Socket socket = serverSocket.accept();
					final InputStream inputStream = socket.getInputStream();
					final DataInputStream dataInputStream = new DataInputStream(inputStream);
					final String in = dataInputStream.readUTF();
										
					final JsonObject msg = JsonParser.parseString(in).getAsJsonObject();
					msg.add("host", new JsonPrimitive(myId));
					
					// See EWD998!RecvMsg.
					msg.add("vc", vc.tickAndMerge(msg.get("vc").getAsJsonObject()));

					// Print the "raw" message after out host has been set and our vector clock has
					// been incremented.
					System.out.println(msg);
					
					inbox.add(msg.get("msg").getAsJsonObject());
					if (msg.get("msg").getAsJsonObject().get("type").getAsString().equals("trm")) {
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
					sendPayload(myId, randomWork.nextInt(nodes.size()));
				} else {					
//					vc.tick();

					final JsonObject json = new JsonObject();
					json.add("host", new JsonPrimitive(myId));
					json.add("src", new JsonPrimitive(myId));
					json.add("rcv", new JsonPrimitive(myId));
					final JsonObject p = new JsonObject();
					p.add("type", new JsonPrimitive("w"));
					json.add("msg", p);
					json.add("vc", vc.tick());
					System.out.println(json.toString());
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
				if (!active) {
//					vc.tick();
					
					final JsonObject json = new JsonObject();
					json.add("host", new JsonPrimitive(myId));
					json.add("src", new JsonPrimitive(myId));
					json.add("rcv", new JsonPrimitive(myId));
					final JsonObject p = new JsonObject();
					p.add("type", new JsonPrimitive("d"));
					json.add("msg", p);
					json.add("vc", vc.tick());
					System.out.println(json.toString());
				}
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
						sendTok(myId, nodes.size() - 1, 0, Color.white);
						color = Color.white;
					} else {
						for (Integer n : nodes.keySet()) {
							sendTrm(myId, n);
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
					sendTok(myId, myId - 1, tokenQ + counter, color == Color.black ? Color.black : tokenColor);
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

	private void sendPayload(final int sender, final int receiver) throws Exception {
		final JsonObject result = new JsonObject();
		result.add("type", new JsonPrimitive("pl"));
		sendMsg(sender, receiver, result);
	}

	private void sendTok(final int sender, final int receiver, final int q, final Color color) throws Exception {
		final JsonObject result = new JsonObject();
		result.add("type", new JsonPrimitive("tok"));
		result.add("q", new JsonPrimitive(q));
		result.add("color", new JsonPrimitive(color.toString()));
		sendMsg(sender, receiver, result);
	}

	private void sendTrm(final int sender, final int receiver) throws Exception {
		final JsonObject result = new JsonObject();
		result.add("type", new JsonPrimitive("trm"));
		sendMsg(sender, receiver, result);
	}

	// Boilerplate: Sending messages. 
	private void sendMsg(final int sender, final int receiver, final JsonObject msg) throws Exception {
		/*
		 * ShiViz regexp: ^{"host":(?<host>[0-9]+),"src":(?<src>[0-9]+),"rcv":(?<rcv>[0-9]+),"msg":(?<event>({"type":"tok","q":-?[0-9]*,"color":"(white|black)"}|{"type":"(pl|trm|w|d)"})),"vc":(?<clock>.*)}
		 */

		final JsonObject json = new JsonObject();
		json.add("host", new JsonPrimitive(sender));
		json.add("src", new JsonPrimitive(sender));
		json.add("rcv", new JsonPrimitive(receiver));
		json.add("msg", msg);
		json.add("vc", vc.tick());
		System.out.println(json);
		
		final Pair p = nodes.get(receiver);		
		int retry = 0;
		while (true) {
			try (Socket socket = new Socket(p.host, p.port)) {
				final OutputStream outputStream = socket.getOutputStream();
				final DataOutputStream dataOutputStream = new DataOutputStream(outputStream);
						
				dataOutputStream.writeUTF(json.toString());
				dataOutputStream.flush();
				dataOutputStream.close();
				
				socket.close();
				return;
			} catch (ConnectException ce) {
				if (retry++ > 3) {
					throw ce;
				}
				Thread.sleep(500L * retry);
			}
		}
	}
	
	public static class Pair {
		public final String host;
		public final int port;

		public Pair(final String host, final int port) {
			this.host = host;
			this.port = port;
		}
	}
}
