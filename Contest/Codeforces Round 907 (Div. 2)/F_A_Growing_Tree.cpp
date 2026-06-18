#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 const int N = 5e5 + 10;
vector<vector<int>> t(N);
int in[N], out[N], Time;
 void euler_tour(int node, int par){
 in[node] = Time++;
 for(auto &child: t[node]){
  if(child != par){
   euler_tour(child, node);
  }
 }
 out[node] = Time++;
}
 struct Segment_Tree{
 int n;
 vector<int> st;
  Segment_Tree(int _n){
  n = _n;
  st.assign(4 * n, 0);
 }
  void update(int node, int b, int e, int &i, int &x){
  if(b == e and e == i){
   st[node] += x;
   return;
  }
  int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
  if(mid >= i)
   update(left, b, mid, i, x);
  else
   update(right, mid + 1, e, i, x);
  st[node] = st[left] + st[right];
 }
  int query(int node, int b, int e, int &l, int &r){
  if(b > r or e < l)
   return 0;
  if(b >= l and e <= r)
   return st[node];
  int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
  return query(left, b, mid, l, r)  + query(right, mid + 1, e, l, r);
 }
  void update(int i, int x){
  update(1, 1, n, i, x);
 }
  int query(int l, int r){
  return query(1, 1, n, l, r);
 }
};
 void solve()
{
 Time = 1;
    int q;
    cin >> q;
    int curr = 1;
    t[curr].clear();
    vector<array<int, 3>> queries(q);
    for(auto &[type, u, v]: queries){
     cin >> type;
     if(type == 1){
      curr++;
      cin >> u;
      t[curr].clear();
      t[u].push_back(curr);
      t[curr].push_back(u);
     }else{
      cin >> u >> v;
     }
    }
    euler_tour(1, -1);
    Segment_Tree st(Time - 1);
    curr = 1;
    for(auto &[type, u, v]: queries){
     if(type == 1){
      curr++;
      int par_sum = st.query(1, in[curr] - 1);
      st.update(in[curr], -par_sum);
      st.update(out[curr], par_sum);
     }else{
      st.update(in[u], v);
      st.update(out[u], -v);
     }
    }
    for(int node = 1; node <= curr; node++){
     cout << st.query(1, in[node]) << (node == curr ? '\n': ' ');
    }
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int tc = 1;
    cin >> tc;
    for (int z = 1; z <= tc; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}