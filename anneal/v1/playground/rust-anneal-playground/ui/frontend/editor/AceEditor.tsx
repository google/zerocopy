import React, { Suspense } from 'react';
import { suspend } from 'suspend-react';

import { useAppSelector } from '../hooks';
import {
  aceKeybinding,
  acePairCharacters,
  aceTheme,
  offerCrateAutocompleteOnUse,
} from '../selectors';
import { CommonEditorProps } from '../types';

const AceEditorDependencies: React.FC<{
  keybinding: string;
  theme: string;
}> = ({ keybinding, theme }) => {
  suspend(
    async (keybinding, theme) => {
      const { importKeybinding, importTheme } = await import('./AceEditorCore');
      await Promise.allSettled([importKeybinding(keybinding), importTheme(theme)]);
    },
    [keybinding, theme, 'AceEditorDependencies'],
  );

  return <></>;
};

const AceEditorLazy = React.lazy(() => import('./AceEditorCore'));

// The ACE editor weighs in at ~250K. Adding all of the themes and the
// (surprisingly chunky) keybindings, it's not that far off from 500K!
//
// To give better initial load performance, we split the editor into a
// separate chunk. As you usually only want one of each theme and
// keybinding, they can also be split, reducing the total size
// transferred.
//
// This also has some benefit if you choose to use the simple editor,
// as ACE should never be loaded.
//
// Themes and keybindings can be changed at runtime.
const AceEditorAsync: React.FC<CommonEditorProps> = (props) => {
  const autocompleteOnUse = useAppSelector(offerCrateAutocompleteOnUse);
  const keybinding = useAppSelector(aceKeybinding);
  const pairCharacters = useAppSelector(acePairCharacters);
  const theme = useAppSelector(aceTheme);

  return (
    <Suspense fallback={'Loading the ACE editor...'}>
      <AceEditorDependencies keybinding={keybinding} theme={theme} />
      <AceEditorLazy
        {...props}
        autocompleteOnUse={autocompleteOnUse}
        keybinding={keybinding}
        pairCharacters={pairCharacters}
        theme={theme}
      />
    </Suspense>
  );
};

export default AceEditorAsync;
