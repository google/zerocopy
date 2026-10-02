// @ts-check
import { fixupPluginRules } from '@eslint/compat';
import eslint from '@eslint/js';
import reactPlugin from 'eslint-plugin-react';
import reactHooksPlugin from 'eslint-plugin-react-hooks';
import tseslint from 'typescript-eslint';

export default tseslint.config(
  eslint.configs.recommended,
  tseslint.configs.recommended,
  reactPlugin.configs.flat.recommended,

  {
    plugins: {
      'react-hooks': fixupPluginRules(reactHooksPlugin),
    },

    settings: {
      react: {
        version: 'detect',
      },
    },

    rules: {
      'no-restricted-syntax': [
        'error',
        {
          message: 'Use `useAppDispatch` instead',
          selector: 'CallExpression[callee.name="useDispatch"]',
        },
        {
          message: 'Use `useAppSelector` instead',
          selector: 'CallExpression[callee.name="useSelector"]',
        },
      ],

      '@typescript-eslint/no-unused-vars': [
        'error',
        {
          args: 'all',
          argsIgnorePattern: '^_',
          caughtErrors: 'all',
          caughtErrorsIgnorePattern: '^_',
          destructuredArrayIgnorePattern: '^_',
          varsIgnorePattern: '^_',
          ignoreRestSiblings: true,
        },
      ],
      '@typescript-eslint/no-use-before-define': [
        'error',
        {
          functions: false,
          variables: false,
        },
      ],

      'react/jsx-boolean-value': ['error', 'never'],

      ...reactHooksPlugin.configs.recommended.rules,
    },
  },
);
