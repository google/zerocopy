--  Driver: makes the 2nd component / K-th element raise and reports how many
--  Finalize calls ran (expected: exactly the number of completed Initialize
--  calls).
with Ada.Text_IO; use Ada.Text_IO;
with Fin_Probe;   use Fin_Probe;
procedure Fin_Main is
begin
   Inits := 0; Fins := 0; Fail_At := 2;
   begin
      Use_Rec;
   exception
      when Constraint_Error => null;
   end;
   Put_Line ("record: inits_attempted=" & Integer'Image (Inits)
             & " finalized=" & Integer'Image (Fins));

   Inits := 0; Fins := 0; Fail_At := 4;
   begin
      Use_Arr (6);
   exception
      when Constraint_Error => null;
   end;
   Put_Line ("array(6), raise at 4th: inits_attempted=" & Integer'Image (Inits)
             & " finalized=" & Integer'Image (Fins));

   Inits := 0; Fins := 0; Fail_At := 0;
   Put_Line ("pick(true)=" & Integer'Image (Pick (True))
             & " pick(false)=" & Integer'Image (Pick (False))
             & " finalized=" & Integer'Image (Fins));
end Fin_Main;
