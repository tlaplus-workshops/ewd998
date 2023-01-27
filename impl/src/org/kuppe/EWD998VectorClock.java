package org.kuppe;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

public class EWD998VectorClock {

	private final int[][] vc;
	// This node's id.
	private final int n;

	public EWD998VectorClock(final int n, final int dimension) {
		this.vc = new int[dimension][dimension];
		this.n = n;
	}

	public EWD998VectorClock tick() {
		// /\ clock' = [ clock EXCEPT ![n][n] = @ + 1 ]
		this.vc[n][n]++;
		return this;
	}

	public void merge(final JsonObject json) {
		final int j = json.get("id").getAsInt();
		
		final JsonArray outer = json.get("clock").getAsJsonArray();
		final JsonArray inner = outer.get(n).getAsJsonArray();

		/*
		 * \* This is where the "magic" of the vector clock happens. /\ LET Max(a,b) ==
		 * IF a < b THEN b ELSE a Merge(r, l) == [ m \in Node |-> IF m = n THEN l[m] + 1
		 * ELSE Max(r[m], l[m]) ] IN clock' = [ clock EXCEPT ![n] =
		 * Merge(inbox[n][j].vc, @) ]
		 */
		this.vc[n][j] = Math.max(this.vc[n][j], inner.get(j).getAsInt());
	}

	public JsonElement toJson() {
		final JsonObject result = new JsonObject();
		result.add("id", new JsonPrimitive(n));
		
		final JsonArray outer = new JsonArray(vc.length);
		for (int i = 0; i < vc.length; i++) {
			JsonArray inner = new JsonArray(vc.length);
			outer.add(inner);
			for (int j = 0; j < vc.length; j++) {
				inner.add(vc[i][j]);
			}
		}
		result.add("clock", outer);

		return result;
	}
}
