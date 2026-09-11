/* global process:false, __dirname:false */

const webpack = require('webpack');
const HtmlPlugin = require('html-webpack-plugin');
const CopyPlugin = require('copy-webpack-plugin');
const MiniCssExtractPlugin = require("mini-css-extract-plugin");
const CompressionPlugin = require("compression-webpack-plugin");
const MonacoWebpackPlugin = require('monaco-editor-webpack-plugin');
const fs = require('node:fs');
const path = require('node:path');

const thisPackage = require('./package.json');
const devDependencies = Object.keys(thisPackage.devDependencies);

const allKeybindingNames =
      fs.globSync('./node_modules/ace-builds/src-noconflict/keybinding-*.js')
      .map(n => path.basename(n))
      .map(n => n.replace(/^keybinding-/, ''))
      .map(n => n.replace(/.js$/, ''));
const allThemeNames =
      fs.globSync('./node_modules/ace-builds/src-noconflict/theme-*.js')
      .map(n => path.basename(n))
      .map(n => n.replace(/^theme-/, ''))
      .map(n => n.replace(/.js$/, ''));
// There's a builtin/default keybinding that we call `ace`.
const allKeybindings = allKeybindingNames.concat(['ace']).sort();
const allThemes = allThemeNames;

// The name is nicer to debug with, but changing names breaks long-term-caching
const developmentFilenameTemplate = '[name]-[contenthash]';
const developmentChunkFilenameTemplate = '[name]-[chunkhash]';

const productionFilenameTemplate = '[contenthash]';
const productionChunkFilenameTemplate = '[chunkhash]';

module.exports = function(_, argv) {
  const isProduction = argv.mode === 'production';
  const filenameTemplate =
        isProduction ?
        productionFilenameTemplate :
        developmentFilenameTemplate;
  const chunkFilenameTemplate =
        isProduction ?
        productionChunkFilenameTemplate :
        developmentChunkFilenameTemplate;

  const devtool =
        isProduction ?
        false :
        'inline-source-map';

  const localIdentName = isProduction ?
         "[hash:base64]" :
         "[path][name]__[local]--[hash:base64]";

  return {
    entry: './index.tsx',

    devtool,

    cache: {
      type: 'filesystem',

      buildDependencies: {
        config: [__filename],
      },
    },

    output: {
      publicPath: 'assets/',
      path: `${__dirname}/build/assets`,
      filename: `${filenameTemplate}.js`,
      chunkFilename: `${chunkFilenameTemplate}.js`,
    },

    resolve: {
      extensions: ['.js', '.jsx', '.ts', '.tsx'],
    },

    module: {
      rules: [
        {
          test: [/\.js$/, /\.jsx$/],
          exclude: /node_modules/,
          use: 'babel-loader',
        },
        {
          test: [/\.ts$/, /\.tsx$/],
          exclude: /node_modules/,
          use: ['babel-loader', 'ts-loader'],
        },
        {
          test: /\.css$/,
          oneOf: [
            // Prism styles as separate files for the shadow DOM
            {
              test: [/prismjs\/themes/, /prismjs-overrides.css$/],
              type: 'asset/resource',
            },

            // Our normal CSS
            {
              test: /\.module.css$/,
              exclude: /node_modules/,
              use: [
                MiniCssExtractPlugin.loader,
                {
                  loader: "css-loader",
                  options: {
                    modules: {
                      localIdentName,
                    },
                  },
                },
                "postcss-loader",
              ],
            },

            // Everything else
            {
              include: /node_modules/,
              use: [
                MiniCssExtractPlugin.loader,
                "css-loader",
                "postcss-loader",
              ],
            },
          ]
        },
        // This inlines the codicon.ttf file from Monaco. Using a
        // regular file fails because it looks for
        // `/assets/assets/...`. Inlining saves a file, and it's
        // pretty small compared to the rest of Monaco.
        {
          test: /\.ttf$/,
          include: /node_modules\/monaco-editor/,
          type: 'asset/inline',
        },
        {
          test: /\.svg$/,
          type: 'asset/inline',
        },
      ],
    },

    plugins: [
      new webpack.DefinePlugin({
        ACE_KEYBINDINGS: JSON.stringify(allKeybindings),
        ACE_THEMES: JSON.stringify(allThemes),
      }),
      new HtmlPlugin({
        title: "Rust Playground",
        template: 'index.ejs',
        filename: '../index.html',
      }),
      new CopyPlugin({
        patterns: [
          { from: 'robots.txt', to: '..' },
        ],
      }),
      new MiniCssExtractPlugin({
        filename: `${filenameTemplate}.css`,
        chunkFilename: `${chunkFilenameTemplate}.css`,
      }),
      new MonacoWebpackPlugin({
        filename: `${filenameTemplate}.worker.js`,
        languages: ["rust"],
      }),
      ...(isProduction ? [new CompressionPlugin()] : []),
    ],

    optimization: {
      splitChunks: {
        chunks: "all",
      },
    },
  };
};
