import { deserialize } from './local_storage';

type ToJson = Parameters<typeof JSON.stringify>[0];

describe('restoring saved state', () => {
  const easyDeserialize = (state: string | ToJson) => {
    if (typeof state === 'string' || state === undefined) {
      return deserialize(state);
    } else {
      state.version = 1;
      return deserialize(JSON.stringify(state));
    }
  };

  test('undefined state stays that way', () => {
    expect(easyDeserialize(undefined)).toBeUndefined();
  });

  test('unknown serialized version resets to defaults', () => {
    expect(easyDeserialize('{"version":42}')).toBeUndefined();
  });

  test('serialized data is kept', () => {
    const parsed = easyDeserialize({
      configuration: { orientation: 'vertical' },
      code: 'not default code',
      notifications: { seenRustSurvey2018: true },
    });

    expect(parsed?.configuration?.orientation).toEqual('vertical');
    expect(parsed?.code).toEqual('not default code');
    expect(parsed?.notifications?.seenRustSurvey2018).toBe(true);
  });

  test('data is migrated', () => {
    const parsed = easyDeserialize({
      configuration: { editor: 'advanced', theme: 'xcode', keybinding: 'vi', pairCharacters: 'disabled' },
    });

    expect(parsed?.configuration?.editor).toEqual('ace');
    expect(parsed?.configuration?.ace?.theme).toEqual('xcode');
    expect(parsed?.configuration?.ace?.keybinding).toEqual('vi');
    expect(parsed?.configuration?.ace?.pairCharacters).toEqual('disabled');
  });
});
