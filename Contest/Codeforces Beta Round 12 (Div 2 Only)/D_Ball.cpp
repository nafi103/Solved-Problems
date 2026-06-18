#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e9 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
 /*
 * Fenwick Tree (1D)
 * 0-indexed implementation.
 * constructor(arr): O(N) linear time construction.
 * query(r): Returns the sum of elements in range [0, r].
 * query(l, r): Returns the sum of elements in range [l, r].
 * add(idx, delta): Adds delta to the element at idx.
 */
template <typename T>
struct Fenwick_Tree{
    int n;
    vector<T> bit;
     Fenwick_Tree(int _n) : n(_n), bit(_n, -inf) {}
     T query(int r) const {
        T mx = -inf;
        for(; r >= 0; r = (r & (r + 1)) - 1)
            mx = max(mx, bit[r]);
        return mx;
    }
     void assign(int idx, T new_val){
        for(; idx < n; idx = idx | (idx + 1)){
            bit[idx] = max(bit[idx], new_val);
        }
    }
};
 void solve()
{
    int n;
    cin >> n;
    vector<array<int, 3>> p(n);
    vector<int> id;
    for(int i = 0; i < n; i++) cin >> p[i][0];
    for(int i = 0; i < n; i++) cin >> p[i][1];
    for(int i = 0; i < n; i++) cin >> p[i][2];
    for(auto &[x, y, z]: p){
        id.push_back(x);
        id.push_back(y);
        id.push_back(z);
    }
    sort(all(p), [&](array<int, 3> &a, array<int, 3> &b){
        return a[0] > b[0];
    });
    sort(all(id));
    id.erase(unique(all(id)), id.end());
    for(auto &[x, y, z]: p){
        x = lower_bound(all(id), x) - id.begin();
        y = lower_bound(all(id), y) - id.begin();
        z = lower_bound(all(id), z) - id.begin();
    }
    int k = sz(id) - 1, ans = 0;
    Fenwick_Tree<int> ft(k + 1);
    for(int i = 0, j = 0; i < n; i++){
        while(p[i][0] != p[j][0]){
            auto &[x, y, z] = p[j];
            ft.assign(k - y, z);
            j++;
        }
        auto &[x, y, z] = p[i];
        if(ft.query(k - y - 1) > z){
            ans++;
        }
    }
    cout << ans << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}