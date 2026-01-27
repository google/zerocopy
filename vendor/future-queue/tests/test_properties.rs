// Copyright (c) The future-queue Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use fnv::FnvHashMap;
use future_queue::{
    traits::{GroupedWeightedFuture, WeightedFuture},
    FutureQueue, FutureQueueContext, FutureQueueGrouped, StreamExt as _,
};
use futures::{future::BoxFuture, stream, Future, FutureExt, Stream, StreamExt as _};
use proptest::prelude::*;
use proptest_derive::Arbitrary;
use std::{borrow::Borrow, collections::HashMap, pin::Pin, sync::Arc, time::Duration};
use tokio::sync::mpsc::UnboundedSender;
use tokio_stream::wrappers::UnboundedReceiverStream;

#[derive(Clone, Debug, Arbitrary)]
struct TestState<G: GroupSpec> {
    #[proptest(strategy = "1usize..64")]
    max_weight: usize,
    #[proptest(strategy = "prop::collection::vec(TestFutureDesc::arbitrary(), 0..512usize)")]
    future_descriptions: Vec<TestFutureDesc<G>>,
    group_desc: G::GroupDesc,
}

#[derive(Copy, Clone, Debug, Arbitrary)]
struct TestFutureDesc<G: GroupSpec> {
    #[proptest(strategy = "duration_strategy()")]
    start_delay: Duration,
    #[proptest(strategy = "duration_strategy()")]
    delay: Duration,
    #[proptest(strategy = "0usize..8")]
    weight: usize,
    #[allow(dead_code)]
    group: G,
}

fn duration_strategy() -> BoxedStrategy<Duration> {
    // Allow for a delay between 0ms and 1000ms uniformly at random.
    (0u64..1000).prop_map(Duration::from_millis).boxed()
}

trait GroupSpec: Arbitrary + Send + Sync + Copy + 'static {
    type Item: Send;
    type GroupDesc;
    type CheckState: Default;

    fn create_stream<'a, St>(stream: St, state: &TestState<Self>) -> BoxedWeightedStream<'a, ()>
    where
        St: Stream<Item = Self::Item> + Send + 'static;

    fn create_stream_item(
        id: usize,
        desc: &TestFutureDesc<Self>,
        future: impl Future<Output = ()> + Send + 'static,
        sender: UnboundedSender<FutureEvent<Self>>,
    ) -> Self::Item;

    fn check_function_called(
        check_state: &mut Self::CheckState,
        id: usize,
        desc: &TestFutureDesc<Self>,
        cx: FutureQueueContext,
    );

    fn check_started(
        check_state: &mut Self::CheckState,
        id: usize,
        desc: &TestFutureDesc<Self>,
        state: &TestState<Self>,
    );

    fn check_finished(
        check_state: &mut Self::CheckState,
        id: usize,
        desc: &TestFutureDesc<Self>,
        state: &TestState<Self>,
    );
}

trait WeightedStream: Stream {
    fn current_weight(&self) -> usize;
}

impl<St, Fut> WeightedStream for FutureQueue<St>
where
    St: Stream<Item = Fut>,
    Fut: WeightedFuture,
{
    fn current_weight(&self) -> usize {
        self.current_weight()
    }
}

impl<St, K, Fut> WeightedStream for FutureQueueGrouped<St, K>
where
    St: Stream<Item = Fut>,
    Fut: GroupedWeightedFuture,
    K: Eq + std::hash::Hash + std::fmt::Debug + Borrow<Fut::Q>,
    Fut::Q: Eq + std::hash::Hash + std::fmt::Debug,
{
    fn current_weight(&self) -> usize {
        self.current_global_weight()
    }
}

type BoxedWeightedStream<'a, Item> = Pin<Box<dyn WeightedStream<Item = Item> + Send + 'a>>;

impl GroupSpec for () {
    type Item = (
        usize,
        Box<dyn FnOnce(FutureQueueContext) -> BoxFuture<'static, ()> + Send + 'static>,
    );
    type GroupDesc = ();
    type CheckState = NonGroupedCheckState;

    fn create_stream<'a, St>(stream: St, state: &TestState<Self>) -> BoxedWeightedStream<'a, ()>
    where
        St: Stream<Item = Self::Item> + Send + 'static,
    {
        Box::pin(stream.future_queue(state.max_weight))
    }

    fn create_stream_item(
        id: usize,
        desc: &TestFutureDesc<Self>,
        future: impl Future<Output = ()> + Send + 'static,
        sender: UnboundedSender<FutureEvent<Self>>,
    ) -> Self::Item {
        (
            desc.weight,
            Box::new(move |cx| {
                sender.send(FutureEvent::FunctionCalled(id, cx)).unwrap();
                future.boxed()
            }),
        )
    }

    fn check_function_called(
        check_state: &mut Self::CheckState,
        id: usize,
        _desc: &TestFutureDesc<Self>,
        cx: FutureQueueContext,
    ) {
        check_state.slots.insert_lowest(cx.global_slot(), id);
    }

    fn check_started(
        check_state: &mut Self::CheckState,
        id: usize,
        desc: &TestFutureDesc<Self>,
        state: &TestState<Self>,
    ) {
        // last_started_id must be 1 less than id.
        let expected_id = check_state.last_started_id.map_or(0, |id| id + 1);
        assert_eq!(
            expected_id, id,
            "expected future id to start != actual id that started"
        );
        check_state.last_started_id = Some(id);

        // Check that current_weight doesn't go over the limit.
        check_state.current_weight += desc.weight.min(state.max_weight);
        assert!(
            check_state.current_weight <= state.max_weight,
            "current weight {} <= max weight {}",
            check_state.current_weight,
            state.max_weight,
        );
    }

    fn check_finished(
        check_state: &mut Self::CheckState,
        id: usize,
        desc: &TestFutureDesc<Self>,
        state: &TestState<Self>,
    ) {
        check_state.current_weight -= desc.weight.min(state.max_weight);
        check_state.slots.remove_slot_for_id(id);
    }
}

#[derive(Debug, Default)]
struct NonGroupedCheckState {
    last_started_id: Option<usize>,
    current_weight: usize,
    slots: SlotMap,
}

#[derive(Clone, Copy, Hash, Eq, PartialEq, Debug, Arbitrary)]
enum TestGroup {
    A,
    B,
    C,
    D,
}

#[derive(Debug, Default)]
struct TestGroupState {
    map: HashMap<TestGroup, usize>,
}

impl Arbitrary for TestGroupState {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        (1usize..64, 1usize..64, 1usize..64, 1usize..64)
            .prop_map(|(a, b, c, d)| {
                let mut map = HashMap::new();
                map.insert(TestGroup::A, a);
                map.insert(TestGroup::B, b);
                map.insert(TestGroup::C, c);
                map.insert(TestGroup::D, d);
                TestGroupState { map }
            })
            .boxed()
    }
}

impl GroupSpec for Option<TestGroup> {
    type Item = (
        usize,
        Option<TestGroup>,
        Box<dyn FnOnce(FutureQueueContext) -> BoxFuture<'static, ()> + Send + 'static>,
    );
    type GroupDesc = TestGroupState;
    type CheckState = GroupedCheckState;

    fn create_stream<'a, St>(stream: St, state: &TestState<Self>) -> BoxedWeightedStream<'a, ()>
    where
        St: Stream<Item = Self::Item> + Send + 'static,
    {
        // Use `Arc` here to ensure that we're using the Borrow functionality.
        let groups = state
            .group_desc
            .map
            .iter()
            .map(|(group, max_weight)| (Arc::new(*group), *max_weight));
        let mut stream = stream.future_queue_grouped(state.max_weight, groups);
        stream.set_extra_verify(true);
        Box::pin(stream)
    }

    fn create_stream_item(
        id: usize,
        desc: &TestFutureDesc<Self>,
        future: impl Future<Output = ()> + Send + 'static,
        sender: UnboundedSender<FutureEvent<Self>>,
    ) -> Self::Item {
        (
            desc.weight,
            desc.group,
            Box::new(move |cx| {
                sender.send(FutureEvent::FunctionCalled(id, cx)).unwrap();
                future.boxed()
            }),
        )
    }

    fn check_function_called(
        check_state: &mut Self::CheckState,
        id: usize,
        desc: &TestFutureDesc<Self>,
        cx: FutureQueueContext,
    ) {
        check_state.global_slots.insert_lowest(cx.global_slot(), id);
        if let Some(group) = desc.group {
            let group_slots = check_state
                .group_slots
                .get_mut(&group)
                .expect("group slot map exists");
            let group_slot = cx
                .group_slot()
                .expect("desc.group is Some so a group slot should be assigned");
            group_slots.insert_lowest(group_slot, id);
        }
    }

    fn check_started(
        check_state: &mut Self::CheckState,
        _id: usize,
        desc: &TestFutureDesc<Self>,
        state: &TestState<Self>,
    ) {
        // Check that current_weight doesn't go over the limit.
        check_state.current_weight += desc.weight.min(state.max_weight);
        assert!(
            check_state.current_weight <= state.max_weight,
            "current weight {} <= max weight {}",
            check_state.current_weight,
            state.max_weight,
        );
        if let Some(group) = desc.group {
            let max_group_weight = state.group_desc.map[&group];
            let current_group_weight = check_state.group_weights.get_mut(&group).unwrap();
            *current_group_weight += desc.weight.min(max_group_weight);
            assert!(
                *current_group_weight <= max_group_weight,
                "current weight {} <= max weight {} for group {:?}",
                *current_group_weight,
                max_group_weight,
                group,
            );
        }
    }

    fn check_finished(
        check_state: &mut Self::CheckState,
        id: usize,
        desc: &TestFutureDesc<Self>,
        state: &TestState<Self>,
    ) {
        check_state.current_weight -= desc.weight.min(state.max_weight);
        check_state.global_slots.remove_slot_for_id(id);

        if let Some(group) = desc.group {
            let current_group_weight = check_state.group_weights.get_mut(&group).unwrap();
            let max_group_weight = state.group_desc.map[&group];
            *current_group_weight -= desc.weight.min(max_group_weight);

            check_state
                .group_slots
                .get_mut(&group)
                .expect("group slot map exists")
                .remove_slot_for_id(id);
        }

        // Note that this code doesn't currently check that futures from this group are
        // preferentially queued up first. That is a surprisingly hard problem that is somewhat
        // low-impact to test (since it falls out of the basic correct implementation).
    }
}

#[derive(Debug)]
struct GroupedCheckState {
    current_weight: usize,
    group_weights: HashMap<TestGroup, usize>,
    // A map of currently-occupied slots, where values are the ID of the future
    // that occupies the slot.
    global_slots: SlotMap,
    // A map of currently-occupied slots for each group.
    group_slots: FnvHashMap<TestGroup, SlotMap>,
}

impl Default for GroupedCheckState {
    fn default() -> Self {
        let mut group_weights = HashMap::new();
        group_weights.insert(TestGroup::A, 0);
        group_weights.insert(TestGroup::B, 0);
        group_weights.insert(TestGroup::C, 0);
        group_weights.insert(TestGroup::D, 0);

        let global_slots = SlotMap::default();
        let mut group_slots = FnvHashMap::default();
        group_slots.insert(TestGroup::A, SlotMap::default());
        group_slots.insert(TestGroup::B, SlotMap::default());
        group_slots.insert(TestGroup::C, SlotMap::default());
        group_slots.insert(TestGroup::D, SlotMap::default());

        GroupedCheckState {
            current_weight: 0,
            group_weights,
            global_slots,
            group_slots,
        }
    }
}

#[derive(Clone, Debug, Default)]
struct SlotMap {
    slots: FnvHashMap<u64, usize>,
}

impl SlotMap {
    fn insert_lowest(&mut self, slot: u64, id: usize) {
        // Check that the slot is currently unoccupied.
        if let Some(existing_id) = self.slots.get(&slot) {
            panic!(
                "slot {} is occupied by future {} (slot map: {:?})",
                slot, existing_id, self.slots
            );
        }

        // Check that the slot is the lowest unoccupied slot.
        for i in 0..slot {
            if !self.slots.contains_key(&i) {
                panic!(
                    "slot {} is not the lowest unoccupied slot (slot map: {:?})",
                    slot, self.slots
                );
            }
        }

        self.slots.insert(slot, id);
    }

    fn slot_for_id(&self, id: usize) -> Option<u64> {
        self.slots.iter().find_map(
            |(slot, slot_id)| {
                if *slot_id == id {
                    Some(*slot)
                } else {
                    None
                }
            },
        )
    }

    fn remove_slot_for_id(&mut self, id: usize) {
        let slot = self
            .slot_for_id(id)
            .unwrap_or_else(|| panic!("id {id} should have had a global slot assigned to it"));
        self.slots.remove(&slot);
    }
}

// ---
// Tests
// ---

#[test]
fn test_examples() {
    let state = TestState {
        max_weight: 1,
        future_descriptions: vec![TestFutureDesc {
            start_delay: Duration::ZERO,
            delay: Duration::ZERO,
            weight: 0,
            group: (),
        }],
        group_desc: (),
    };
    test_future_queue_impl(state);

    let state = TestState {
        max_weight: 1,
        future_descriptions: vec![TestFutureDesc {
            start_delay: Duration::ZERO,
            delay: Duration::ZERO,
            weight: 0,
            group: None,
        }],
        group_desc: TestGroupState {
            map: maplit::hashmap! {TestGroup::A => 1, TestGroup::B => 1, TestGroup::C => 1, TestGroup::D => 1},
        },
    };
    test_future_queue_impl(state);
}

proptest! {
    #[test]
    fn proptest_future_queue(state: TestState<()>) {
        test_future_queue_impl(state)
    }

    #[test]
    fn proptest_future_queue_grouped(state: TestState<Option<TestGroup>>) {
        test_future_queue_impl(state)
    }
}

#[derive(Clone, Debug)]
enum FutureEvent<G: GroupSpec> {
    FunctionCalled(usize, FutureQueueContext),
    Started(usize, TestFutureDesc<G>),
    Finished(usize, TestFutureDesc<G>),
}

fn test_future_queue_impl<G: GroupSpec>(state: TestState<G>) {
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_time()
        .start_paused(true)
        .build()
        .expect("tokio builder succeeded");
    let (sender, mut receiver) = tokio::sync::mpsc::unbounded_channel();
    let (item_sender, item_receiver) = tokio::sync::mpsc::unbounded_channel();

    let futures = state
        .future_descriptions
        .iter()
        .enumerate()
        .map(move |(id, desc)| {
            let desc = *desc;
            let sender = sender.clone();
            let item_sender = item_sender.clone();
            async move {
                // First, sleep for this long.
                tokio::time::sleep(desc.start_delay).await;
                // For each description, create a future.
                let sender2 = sender.clone();
                let delay_fut = async move {
                    // Send the fact that this future started to the mpsc queue.
                    sender2
                        .send(FutureEvent::Started(id, desc))
                        .expect("receiver held open by loop");
                    tokio::time::sleep(desc.delay).await;
                    sender2
                        .send(FutureEvent::Finished(id, desc))
                        .expect("receiver held open by loop");
                };
                // Errors should never occur here.
                if let Err(err) =
                    item_sender.send(G::create_stream_item(id, &desc, delay_fut, sender))
                {
                    panic!("future_receiver held open by loop: {}", err);
                }
            }
        })
        .collect::<Vec<_>>();
    let combined_future = stream::iter(futures).buffer_unordered(1).collect::<()>();
    runtime.spawn(combined_future);

    // We're going to use item_receiver as a stream.
    let stream = UnboundedReceiverStream::new(item_receiver);

    let mut completed_map = vec![false; state.future_descriptions.len()];
    let mut check_state = G::CheckState::default();

    runtime.block_on(async move {
        // Record values that have been completed in this map.
        let mut stream = G::create_stream(stream, &state);
        let mut receiver_done = false;
        loop {
            tokio::select! {
                // biased ensures that the receiver is drained before the stream is polled. Without
                // it, it's possible that we fail to record the completion of some futures in status_map.
                biased;

                recv = receiver.recv(), if !receiver_done => {
                    match recv {
                        Some(FutureEvent::FunctionCalled(id, cx)) => {
                            // Ensure that the ID has not been seen before.
                            assert!(!completed_map[id], "FunctionCalled for fresh future");
                            G::check_function_called(&mut check_state, id, &state.future_descriptions[id], cx);
                        }
                        Some(FutureEvent::Started(id, desc)) => {
                            G::check_started(&mut check_state, id, &desc, &state);
                        }
                        Some(FutureEvent::Finished(id, desc)) => {
                            // Record that this value was completed.
                            completed_map[id] = true;
                            G::check_finished(&mut check_state, id, &desc, &state);
                        }
                        None => {
                            // All futures finished -- going to check for completion in stream.next() below.
                            receiver_done = true;
                        }
                    }
                }
                next = stream.next() => {
                    if next.is_none() {
                        assert_eq!(stream.current_weight(), 0, "all futures complete => current weight is 0");
                        break;
                    }
                }
                else => {
                    tokio::time::advance(Duration::from_millis(1)).await;
                }
            }
        }

        // Check that all futures completed.
        let not_completed: Vec<_> = completed_map
            .iter()
            .enumerate()
            .filter(|(_, v)| !*v).map(|(n, _)| n.to_string())
            .collect();
        if !not_completed.is_empty() {
            let not_completed_ids = not_completed.join(", ");
            panic!("some futures did not complete: {}", not_completed_ids);
        }
    })
}
