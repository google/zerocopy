//! Setup unicode-formatted table for prettytable
//!
//! TODO: Move to separate crate

use prettytable::format;
use prettytable::Table;

fn format_table(table: &mut Table) {
    table.set_format(
        format::FormatBuilder::new()
            .column_separator('│')
            .borders('│')
            .separators(
                &[format::LinePosition::Top],
                format::LineSeparator::new('─', '┬', '┌', '┐'),
            )
            .separators(
                &[format::LinePosition::Title],
                format::LineSeparator::new('─', '┼', '├', '┤'),
            )
            .separators(
                &[format::LinePosition::Intern],
                format::LineSeparator::new('─', '┼', '├', '┤'),
            )
            .separators(
                &[format::LinePosition::Bottom],
                format::LineSeparator::new('─', '┴', '└', '┘'),
            )
            .padding(1, 1)
            .build(),
    );
}
/// Returns Table with unicode formatter
pub fn new() -> Table {
    let mut table = Table::new();
    format_table(&mut table);
    table
}
