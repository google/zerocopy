/* global ACE_KEYBINDINGS:false, ACE_THEMES:false */

import React from 'react';

import { Either as EitherConfig, Select as SelectConfig } from './ConfigElement';
import MenuGroup from './MenuGroup';
import SimpleButtonMenuItem from './SimpleButtonMenuItem';
import { useAppDispatch, useAppSelector } from './hooks';
import * as client from './reducers/client';
import * as config from './reducers/configuration';
import {
  AssemblyFlavor,
  DemangleAssembly,
  Editor,
  Orientation,
  PairCharacters,
  ProcessAssembly,
  Theme,
} from './types';

const MONACO_THEMES = [
  'vs', 'vs-dark', 'vscode-dark-plus',
];

const ConfigMenu: React.FC = () => {
  'use memo';

  const keybinding = useAppSelector((state) => state.configuration.ace.keybinding);
  const aceTheme = useAppSelector((state) => state.configuration.ace.theme);
  const monacoTheme = useAppSelector((state) => state.configuration.monaco.theme);
  const theme = useAppSelector((state) => state.configuration.theme);
  const orientation = useAppSelector((state) => state.configuration.orientation);
  const editorStyle = useAppSelector((state) => state.configuration.editor);
  const pairCharacters = useAppSelector((state) => state.configuration.ace.pairCharacters);
  const assemblyFlavor = useAppSelector((state) => state.configuration.assemblyFlavor);
  const demangleAssembly = useAppSelector((state) => state.configuration.demangleAssembly);
  const processAssembly = useAppSelector((state) => state.configuration.processAssembly);

  const dispatch = useAppDispatch();

  return (
    <>
      <MenuGroup title="Editor">
        <SelectConfig
          name="Editor"
          value={editorStyle}
          onChange={(e) => dispatch(config.changeEditor(e))}
        >
          {[Editor.Simple, Editor.Ace, Editor.Monaco]
            .map(k => <option key={k} value={k}>{k}</option>)}
        </SelectConfig>
        {editorStyle === Editor.Ace && (
          <>
            <SelectConfig
              name="Keybinding"
              value={keybinding}
              onChange={(k) => dispatch(config.changeKeybinding(k))}
            >
              {ACE_KEYBINDINGS.map(k => <option key={k} value={k}>{k}</option>)}
            </SelectConfig>

            <SelectConfig
              name="Theme"
              value={aceTheme}
              onChange={(t) => dispatch(config.changeAceTheme(t))}
            >
              {ACE_THEMES.map(t => <option key={t} value={t}>{t}</option>)}
            </SelectConfig>

            <EitherConfig
              id="editor-pair-characters"
              name="Pair Characters"
              a={PairCharacters.Enabled}
              b={PairCharacters.Disabled}
              value={pairCharacters}
              onChange={(p) => dispatch(config.changePairCharacters(p))} />
          </>
        )}
        {editorStyle === Editor.Monaco && (
          <>
            <SelectConfig
              name="Theme"
              value={monacoTheme}
              onChange={(t) => dispatch(config.changeMonacoTheme(t))}
            >
              {MONACO_THEMES.map(t => <option key={t} value={t}>{t}</option>)}
            </SelectConfig>
          </>
        )}
      </MenuGroup>

      <MenuGroup title="UI">
        <SelectConfig name="Theme" value={theme} onChange={(t) => dispatch(config.changeTheme(t))}>
          <option value={Theme.System}>System</option>
          <option value={Theme.Light}>Light</option>
          <option value={Theme.Dark}>Dark</option>
        </SelectConfig>

        <SelectConfig
          name="Orientation"
          value={orientation}
          onChange={(o) => dispatch(config.changeOrientation(o))}
        >
          <option value={Orientation.Automatic}>Automatic</option>
          <option value={Orientation.Horizontal}>Horizontal</option>
          <option value={Orientation.Vertical}>Vertical</option>
        </SelectConfig>
      </MenuGroup>

      <MenuGroup title="Assembly">
        <EitherConfig
          id="assembly-flavor"
          name="Flavor"
          a={AssemblyFlavor.Att}
          b={AssemblyFlavor.Intel}
          aLabel="AT&T"
          bLabel="Intel"
          value={assemblyFlavor}
          onChange={(a) => dispatch(config.changeAssemblyFlavor(a))} />

        <EitherConfig
          id="assembly-symbols"
          name="Symbol Demangling"
          a={DemangleAssembly.Demangle}
          b={DemangleAssembly.Mangle}
          aLabel="On"
          bLabel="Off"
          value={demangleAssembly}
          onChange={(d) => dispatch(config.changeDemangleAssembly(d))}
        />

        <EitherConfig
          id="assembly-view"
          name="Name Filtering"
          a={ProcessAssembly.Filter}
          b={ProcessAssembly.Raw}
          aLabel="On"
          bLabel="Off"
          value={processAssembly}
          onChange={(p) => dispatch(config.changeProcessAssembly(p))}
        />
      </MenuGroup>

      <MenuGroup title="Reset">
        <SimpleButtonMenuItem onClick={() => dispatch(client.showConfigReset())}>
          Reset all code and configuration to default values
        </SimpleButtonMenuItem>
      </MenuGroup>
    </>
  );
};

export default ConfigMenu;
