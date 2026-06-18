#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 struct Segment_Tree{
 vector<int> v, st;
  Segment_Tree(vector<int> &_v, int n){
  v = _v;
  st.resize(4 * n);
  build(1,1,n);
 }
  void build(int node, int b, int e){
  if(b == e){
   st[node] = v[b];
   return;
  }
  int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
  build(left, b, mid);
  build(right, mid + 1, e);
  st[node] = max(st[left], st[right]);
 }
  int query(int node, int b, int e, int &l, int &r){
  if(b > r or e < l)
   return 0;
  if(b >= l and e <= r)
   return st[node];
  int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
  return max(query(left, b, mid, l, r), query(right, mid + 1, e, l, r));
 }
};
 void solve()
{
    int n, m;
    cin >> n >> m;
    vector<int> v(m+1);
    for(int i = 1; i <= m; i++)
     cin >> v[i];
    Segment_Tree st(v, m);
    int q;
    cin >> q;
    while(q--){
     int sr, sc, er, ec, k;
     cin >> sr >> sc >> er >> ec >> k;
     int max_row = ((n - sr) / k) * k + sr;
     if(sc > ec)
      swap(sc, ec);
     if(abs(sr - er) % k == 0 and abs(sc - ec) % k ==0 and st.query(1,1,m,sc,ec) < max_row)
      cout << "YES" << endl;
     else
      cout << "NO"<< endl;
    }
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}