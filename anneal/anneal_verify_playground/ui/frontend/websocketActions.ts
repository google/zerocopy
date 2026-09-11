import { PayloadAction, isAction } from '@reduxjs/toolkit';
import z from 'zod';

export type WsPayloadAction<P = void, T extends string = string> = PayloadAction<
  P,
  T,
  { sequenceNumber: number }
>;

export const createWebsocketResponseAction = <P, T extends string = string>(type: T) => {
  function actionCreator(): WsPayloadAction<P> {
    throw 'Should never be executed by JS';
  }
  actionCreator.type = type;
  actionCreator.match = function (action: unknown): action is WsPayloadAction<P, T> {
    return isAction(action) && action.type === type;
  };

  return actionCreator;
};

export const createWebsocketResponseSchema = <P extends z.ZodTypeAny, T extends string = string>(
  creator: { type: T },
  payload: P,
) =>
  z.object({
    type: z.literal(creator.type),
    payload,
    meta: z.object({
      // deliberately omitting `websocket` to avoid sending the server's
      // responses back to the server infinitely
      sequenceNumber: z.number(),
    }),
  });

export const createWebsocketResponse = <T extends string, P extends z.ZodTypeAny>(
  type: T,
  payloadSchema: P,
) => {
  type Payload = z.infer<typeof payloadSchema>;
  const action = createWebsocketResponseAction<Payload>(type);
  const schema = createWebsocketResponseSchema(action, payloadSchema);

  return { action, schema };
};

const nextSequenceNumber = (() => {
  let sequenceNumber = 0;
  return () => sequenceNumber++;
})();

export const makeWebSocketMeta = () => ({
  websocket: true,
  sequenceNumber: nextSequenceNumber(),
});
