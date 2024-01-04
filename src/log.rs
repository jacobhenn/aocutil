use std::{
    cell::{Cell, RefCell},
    fmt,
    sync::RwLock,
};

use ansi_term::{Color, Style};

use tracing::{span, Event, Level, Metadata, Subscriber};
use tracing_subscriber::{
    fmt::{
        format::{DefaultFields, Writer},
        FmtContext, FormatEvent, FormatFields, FormattedFields,
    },
    layer::SubscriberExt,
    registry::{LookupSpan, Registry},
    util::SubscriberInitExt,
    EnvFilter,
};

/// Extremely clumsy tree-formatted logger
// TODO: this is just silly. implement this as a proper Layer or something
pub struct TreeFormatter {
    current_path: RwLock<Vec<span::Id>>,
}

impl TreeFormatter {
    fn new() -> Self {
        Self {
            current_path: RwLock::new(Vec::new()),
        }
    }

    fn fmt_leading(writer: &mut Writer<'_>, metadata: &Metadata) -> fmt::Result {
        let color = if metadata.level() == &Level::ERROR {
            Color::Red
        } else if metadata.level() == &Level::WARN {
            Color::Yellow
        } else if metadata.level() == &Level::INFO {
            Color::Green
        } else if metadata.level() == &Level::DEBUG {
            Color::Blue
        } else if metadata.level() == &Level::TRACE {
            Color::Purple
        } else {
            Color::White
        };

        let level_str = metadata.level().to_string();
        write!(writer, "{}", color.paint(level_str))?;

        let target_str = metadata.target().to_string();
        write!(writer, " {}", Color::Cyan.paint(target_str))?;

        if let Some(line) = metadata.line() {
            let line_str = format!(":{}", line);
            write!(writer, "{}", Color::Cyan.paint(line_str))?;
        }

        Ok(())
    }

    fn fmt_indent(writer: &mut Writer<'_>, level: usize) -> fmt::Result {
        for _ in 0..level {
            write!(writer, "{}   ", Color::Black.paint("│"))?;
        }

        Ok(())
    }
}

impl<S, N> FormatEvent<S, N> for TreeFormatter
where
    S: Subscriber + for<'a> LookupSpan<'a>,
    N: for<'a> FormatFields<'a> + 'static,
{
    fn format_event(
        &self,
        ctx: &FmtContext<'_, S, N>,
        mut writer: Writer<'_>,
        event: &Event<'_>,
    ) -> fmt::Result {
        let mut change_idx = None;

        if let Some(scope) = ctx.event_scope() {
            let mut i = 0;
            for span in scope.from_root() {
                if self.current_path.read().unwrap().get(i) != Some(&span.id()) {
                    if change_idx.is_none() {
                        change_idx = Some(i);
                        self.current_path.write().unwrap().truncate(i);
                    }

                    self.current_path.write().unwrap().push(span.id());
                }
                i += 1;
            }

            if i < self.current_path.read().unwrap().len() {
                self.current_path.write().unwrap().truncate(i);
            }
        }

        if let Some(i) = change_idx {
            for (i, span) in ctx.event_scope().unwrap().from_root().enumerate().skip(i) {
                Self::fmt_leading(&mut writer, span.metadata())?;

                write!(writer, " ")?;

                Self::fmt_indent(&mut writer, i)?;

                write!(writer, "{}", Style::new().bold().paint(span.name()))?;

                let ext = span.extensions();
                let fields = ext
                    .get::<FormattedFields<N>>()
                    .expect("will never be `None`");

                if !fields.is_empty() {
                    write!(writer, " {}", fields)?;
                }

                writeln!(writer)?;
            }
        }

        Self::fmt_leading(&mut writer, event.metadata())?;

        write!(writer, " ")?;

        Self::fmt_indent(&mut writer, self.current_path.read().unwrap().len())?;

        ctx.field_format().format_fields(writer.by_ref(), event)?;

        writeln!(writer)
    }
}

pub fn default_subscriber() -> impl SubscriberInitExt {
    // tracing_subscriber::fmt()
    //     .with_env_filter(EnvFilter::from_default_env())
    //     .without_time()
    //     .with_target(false)
    //     .with_line_number(true)

    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .event_format(TreeFormatter::new())
}

pub fn test_subscriber() -> impl SubscriberInitExt {
    // tracing_subscriber::fmt()
    //     .with_env_filter(EnvFilter::from_default_env())
    //     .without_time()
    //     .with_target(false)
    //     .with_line_number(true)
    //     .with_test_writer()

    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .event_format(TreeFormatter::new())
        .with_test_writer()
}
