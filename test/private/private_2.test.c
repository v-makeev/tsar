int main() {
  int I, X;
  #pragma sapfor analysis firstprivate(X) secondtolastprivate(X) dependency(I)
  for (I = 0; I < 10; ++I)
    X = I;
  X = 2 * X;
  return 0;
}