#include <bits/stdc++.h>
 using namespace std;
 int main() {
 ios_base::sync_with_stdio(0), cin.tie(0), cout.tie(0);
 string a;
 cin >> a;
 int k;
 cin >> k;
 string v[k];
 for (int i = 0; i < (int)a.size(); i++) {
  v[i%k].push_back(a[i]);
 }
 for (int i = 0; i < k; i++)
  sort(v[i].begin(), v[i].end());
 for (int i = 0; i < (int)a.size(); i++)
  cout << v[i%k][i/k];
 cout << '\n';
}