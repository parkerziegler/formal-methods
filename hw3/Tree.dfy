datatype Option<T> = None | Some(T)
datatype Tree = Leaf | Node(Tree, int, Tree)

function Contains(t : Tree, v : int) : bool
{
    match t
    case Leaf => false
    case Node(left, x, right) =>
        x == v || Contains(left, v) || Contains(right, v)

}

function Ordered(t : Tree) : bool
{
    // TODO: Implement this.
}

function Size(t : Tree) : int
{
    // TODO: Implement this.
}

method Insert(t : Tree, v : int) returns (tp : Tree)
  requires Ordered(t)
  ensures Ordered(tp) 
  // TODO: Add additional post-conditions here.
{
    // TODO: Implement this.
}

method Min(t : Tree) returns (m : Option<int>)
  requires Ordered(t)
  ensures (t.Leaf?) <==> (m.None?) // tree empty.
  ensures (t.Node?) <==> (m.Some?) // tree non-empty.
  ensures (t.Node?) ==> Contains(t, m.value) // must return value from the tree.
  ensures (t.Node?) ==> (forall v :: Contains(t, v) ==> m.value <= v); // is min
  // TODO: Add additional post-conditions here.
{
    // TODO: Implement this.
}

function Count(t : Tree, v : int) : int
  ensures Count(t, v) >= 0;
{
    // TODO: Implement this.
}

lemma Lemma_CountEquivContains(t : Tree, v : int)
  ensures Contains(t, v) <==> (Count(t, v) > 0)
{
    // TODO: Prove this.
}

method Remove(t : Tree, v : int) returns (tp : Tree)
  requires Ordered(t)
  ensures Ordered(tp)
  // TODO: State remaining post-conditions. 
{
    // TODO: Implement this.
}
