--  Driver variant: traces which array elements are finalized when the
--  4th of 6 element Initialize calls raises. V records the order in which
--  Initialize completed (0 = Initialize never completed for that element).
with Ada.Text_IO; use Ada.Text_IO;
with Fin_Probe;   use Fin_Probe;
procedure Trace_Main is
begin
   Trace := True;
   Inits := 0; Fins := 0; Fail_At := 4;
   begin
      Use_Arr (6);
   exception
      when Constraint_Error => null;
   end;
   New_Line;
   Put_Line ("completed_initialize=3 finalize_calls=" & Integer'Image (Fins));
end Trace_Main;
