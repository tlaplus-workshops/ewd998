package org.kuppe;

import java.util.HashMap;
import java.util.Map;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.reflect.TypeToken;

public class EWD998VectorClock {

	private final int[] vc;
	// This node's id.
	private final int n;

	public EWD998VectorClock(final int n, final int dimension) {
		this.vc = new int[dimension];
		this.n = n;
	}

	public synchronized JsonElement tick() {
		// /\ clock' = [ clock EXCEPT ![n][n] = @ + 1 ]
		this.vc[n]++;
		return toJson();
	}

	public synchronized JsonElement tickAndMerge(final JsonObject json) {
		// Each time a process receives a message, it increments its own logical clock
		// in the vector by one and updates each element in its vector by taking the
		// maximum of the value in its own vector clock and the value in the vector in
		// the received message (for every element).
		// https://en.wikipedia.org/wiki/Vector_clock
		tick();
		
		// De-serialize.
		final TypeToken<Map<String, Integer>> typeToken = new TypeToken<Map<String, Integer>>() { };
		final Map<String, Integer> m = new Gson().fromJson(json, typeToken.getType());
		
		/*
		 * This is where the "magic" of the vector clock happens. 
		 * 
		 * /\ LET Max(a,b) == IF a < b THEN b ELSE a
		 *  
		 *        Merge(r, l) == [ m \in Node |-> IF m = n THEN l[m] + 1
		 *                                    ELSE Max(r[m], l[m]) ]
		 *                                    
		 *    IN clock' = [ clock EXCEPT ![n] = Merge(inbox[n][j].vc, @) ]
		 */
		for (int i = 0; i < m.size(); i++) {
			this.vc[i] = Math.max(this.vc[i], m.get(Integer.toString(i)));
		}
		
		return toJson();
	}

	private JsonElement toJson() {
		Map<String, Integer> m = new HashMap<>();
		for (int i = 0; i < vc.length; i++) {
			m.put(Integer.toString(i), vc[i]);
		}
		return new Gson().toJsonTree(m);
	}
}
