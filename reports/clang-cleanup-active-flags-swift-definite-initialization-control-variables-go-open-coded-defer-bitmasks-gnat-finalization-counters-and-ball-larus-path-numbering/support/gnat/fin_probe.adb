with Ada.Text_IO;
package body Fin_Probe is
   overriding procedure Initialize (X : in out Ctrl) is
   begin
      Inits := Inits + 1;
      if Inits = Fail_At then
         raise Constraint_Error;
      end if;
      X.V := Inits;
   end Initialize;

   overriding procedure Finalize (X : in out Ctrl) is
   begin
      Fins := Fins + 1;
      if Trace then
         Ada.Text_IO.Put (" fin(V=" & Integer'Image (X.V) & ")");
      end if;
   end Finalize;

   function Make (V : Integer) return Ctrl is
   begin
      return (Ada.Finalization.Controlled with V => V);
   end Make;

   --  Default initialization of a record whose second component may raise.
   procedure Use_Rec is
      R : Rec3;
   begin
      Inits := Inits + R.C.V;
   end Use_Rec;

   --  Default initialization of an array whose K-th element may raise.
   procedure Use_Arr (N : Positive) is
      A : Arr (1 .. N);
   begin
      Inits := Inits + A (N).V;
   end Use_Arr;

   --  Two scope objects; the second is elaborated only if the first
   --  elaboration completed.
   procedure Use_Block (Flag : Boolean) is
      X : Ctrl;
      Y : Ctrl := Make (if Flag then 1 else 2);
   begin
      Inits := Inits + X.V + Y.V;
   end Use_Block;

   --  A controlled temporary created in one arm of a conditional expression.
   function Pick (Flag : Boolean) return Integer is
   begin
      return (if Flag then Make (3).V else 0);
   end Pick;
end Fin_Probe;
