--  Probe: finalization state for partially initialized controlled
--  composites in an Ada compiler.
with Ada.Finalization;
package Fin_Probe is
   type Ctrl is new Ada.Finalization.Controlled with record
      V : Integer := 0;
   end record;
   overriding procedure Initialize (X : in out Ctrl);
   overriding procedure Finalize (X : in out Ctrl);

   Fail_At : Integer := 0;     --  Initialize raises when this count is reached
   Inits, Fins : Integer := 0;
   Trace : Boolean := False;   --  print V of each finalized element

   --  A record with three controlled components (one component list).
   type Rec3 is record
      A, B, C : Ctrl;
   end record;

   --  An array of controlled elements.
   type Arr is array (Positive range <>) of Ctrl;

   procedure Use_Rec;
   procedure Use_Arr (N : Positive);
   procedure Use_Block (Flag : Boolean);
   function Pick (Flag : Boolean) return Integer;
end Fin_Probe;
