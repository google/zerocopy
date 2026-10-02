module.exports = {
  plugins: [
    require('postcss-simple-vars'),
    require('postcss-nesting'),
    require('postcss-mixins'),
    require('autoprefixer')(),
  ],
};
