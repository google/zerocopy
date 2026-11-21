--  Prints the storage size of the runtime record that tracks one
--  finalizable object (Master_Node) and of a finalization master.
with Ada.Text_IO; use Ada.Text_IO;
with System.Finalization_Primitives; use System.Finalization_Primitives;
procedure Node_Size is
begin
   Put_Line ("Master_Node'Size (bits) =" & Integer'Image (Master_Node'Size));
   Put_Line ("Master_Node'Max_Size_In_Storage_Elements (bytes) ="
             & Integer'Image (Master_Node'Max_Size_In_Storage_Elements));
   Put_Line ("Integer'Size (bits) =" & Integer'Image (Integer'Size));
end Node_Size;
