# Informal solution

The displayed domain of \(\varphi\) must be read as \(\mathbb R^2\), since
\(\varphi(s,-s)\) has two arguments. For
\(\varphi\in C_c^\infty(\mathbb R^2)\),
\[
  \langle T,\varphi\rangle=\int_{\mathbb R}\varphi(s,-s)\,ds
\]
is integration against the locally finite measure carried by the line
\(y=-x\). It is therefore a distribution (indeed a tempered distribution).

With the Fourier convention
\(\widehat u(\xi)=\int e^{-ix\cdot\xi}u(x)\,dx\), its transform is
\[
  \widehat T(\xi,\eta)=2\pi\,\delta(\xi-\eta).
\]
This follows by writing the phase on the line as
\(e^{-is(\xi-\eta)}\) and using the Fourier transform of the constant
function (1). Other normalizations move the factor (2\pi).

By definition of distributional differentiation,
\[
 \langle \partial_xT,\varphi\rangle=-\int_{\mathbb R}
 \partial_x\varphi(s,-s)\,ds.
\]
Also
\(\frac d{ds}\varphi(s,-s)=\partial_x\varphi(s,-s)-
\partial_y\varphi(s,-s)\). Its integral vanishes by compact support, hence
\(\partial_xT=\partial_yT\). Differentiating this identity once more gives
\(\partial_x^2T=\partial_x\partial_yT=\partial_y^2T\), and consequently
\[
  (\partial_x^2-\partial_y^2)T=0.
\]
