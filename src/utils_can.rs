// copyright Matthias Behr, (c) 2022
//
// todos:
//
use super::utils::decode_frame_payload;
use crate::utils::buf_as_hex_to_io_write;
use afibex::fibex::{FibexData, FibexError};
use lazy_static::lazy_static;
use std::io::Write;

lazy_static! {
    static ref NO_CHANNEL_NAME: String = "<no CHANNEL NAME>".to_string();
}
/// find the frame_ref and return the channel short_name and the frame_ref
fn find_frame_ref(
    fd: &FibexData,
    channel_id: &Option<&String>,
    frame_id: u32,
) -> Option<(String, String)> {
    if let Some(channel_id) = channel_id {
        if let Some(channel) = fd.elements.channels.get(*channel_id) {
            return channel
                .frame_ref_by_frame_triggering_identifier
                .get(&frame_id)
                .map(|frame_id| {
                    (
                        channel.short_name.as_ref().unwrap_or(channel_id).to_owned(),
                        frame_id.to_owned(),
                    )
                });
        }
    } else {
        // wildcard search
        for (channel_name, channel) in &fd.elements.channels {
            if let Some(frame_ref) = channel
                .frame_ref_by_frame_triggering_identifier
                .get(&frame_id)
            {
                return Some((
                    channel
                        .short_name
                        .as_ref()
                        .unwrap_or(channel_name)
                        .to_owned(),
                    frame_ref.to_owned(),
                ));
            }
        }
    }
    None
}

/// decode a CAN frame and payload according
/// into a string that follows the conventions:
/// - symbol for rx (>), tx(<)
/// - channel short-name
/// - (frame-id in hex)
/// - frame name
/// - payload (as json parseable string). Line breaks in strings will be replaced by spaces
///
/// channel_id can be empty, then the first channel with that frame_id is used
pub fn decode_can_frame(
    fd: &FibexData,
    is_rx: bool,
    channel_id: &Option<&String>,
    frame_id: u32,
    payload: &[u8],
    decode_payload: bool,
    decode_compu_methods: bool,
) -> Result<String, FibexError> {
    if frame_id == 0 {
        Err(FibexError::new("can: frame_id 0 is invalid"))
    } else {
        let mut writer = Vec::with_capacity(2 * 1024); // todo better heuristics?

        // find frame for channel_id/frame_id
        if let Some((channel_name, frame_ref)) = find_frame_ref(fd, channel_id, frame_id) {
            // find that frame:
            write!(
                writer,
                "{} {} 0x{:03x}",
                if is_rx { '>' } else { '<' },
                channel_name,
                frame_id,
            )
            .map_err(|e| FibexError { msg: e.to_string() })?;
            if let Some(frame) = fd.elements.frames_map_by_id.get(&frame_ref) {
                if let Some(short_name) = &frame.short_name {
                    write!(writer, " {} ", short_name)
                        .map_err(|e| FibexError { msg: e.to_string() })?;
                } else {
                    write!(writer, " <no short-name id={}> ", frame.id)
                        .map_err(|e| FibexError { msg: e.to_string() })?;
                }
                // write raw payload
                write!(writer, "[").map_err(|e| FibexError { msg: e.to_string() })?;
                buf_as_hex_to_io_write(&mut writer, payload)
                    .map_err(|e| FibexError { msg: e.to_string() })?;
                write!(writer, "]").map_err(|e| FibexError { msg: e.to_string() })?;

                if decode_payload {
                    write!(writer, ":").map_err(|e| FibexError { msg: e.to_string() })?;
                    decode_frame_payload(frame, &mut writer, fd, payload, decode_compu_methods)
                        .map_err(|e| FibexError { msg: e.to_string() })?;
                }
            } else {
                write!(
                    writer,
                    " <frame_ref {} not found!> {:?}",
                    frame_ref, payload
                )
                .map_err(|e| FibexError { msg: e.to_string() })?;
            }
        } else {
            // frame id unknown: output just the payload
            write!(
                writer,
                "{} {} 0x{:03x} <unknown frame> ",
                if is_rx { '>' } else { '<' },
                if let Some(channel_id) = channel_id {
                    let name = fd
                        .elements
                        .channels
                        .get(*channel_id)
                        .and_then(|c| c.short_name.as_ref())
                        .unwrap_or(channel_id);
                    name
                } else {
                    &NO_CHANNEL_NAME
                },
                frame_id,
            )
            .map_err(|e| FibexError { msg: e.to_string() })?;
            write!(writer, "[").map_err(|e| FibexError { msg: e.to_string() })?;
            buf_as_hex_to_io_write(&mut writer, payload)
                .map_err(|e| FibexError { msg: e.to_string() })?;
            write!(writer, "]").map_err(|e| FibexError { msg: e.to_string() })?;
        }
        let res = unsafe { String::from_utf8_unchecked(writer) }; // we do know its proper utf8 strings... (todo ensure for each encoding!)
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn frame_id_0() {
        let fd = FibexData::new();

        let r = decode_can_frame(&fd, true, &None, 0, &[], false, false);
        assert!(r.is_err());
    }

    // todo create test fibex...

}
