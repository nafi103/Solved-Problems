#include <bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
 using namespace std;
using namespace chrono;
using namespace __gnu_pbds;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T>
using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update>;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)         \
    cerr << #x << " = "; \
    _print(x);           \
    cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
int ans = 0;
vector<vector<int>> t;
vector<int> subtree_size;
 void dfs(int node)
{
    int mx_child = 0;
    unordered_map<int, int> cnt;
    subtree_size[node] = 1;
    for (auto &child : t[node])
    {
        dfs(child);
        subtree_size[node] += subtree_size[child];
        mx_child = max(mx_child, subtree_size[child]);
        cnt[subtree_size[child]]++;
    }
    if(mx_child*2>=(subtree_size[node]-1)){
        ans += mx_child * (subtree_size[node] - 1 - mx_child);
        return;
    }
    vector<bool> dp(subtree_size[node],false);
    dp[0] = 1;
    for(auto &[len, c]: cnt){
        int g = 1;
        while(g<=c){
            int j = len * g;
            for (int i = subtree_size[node] - 1; i >= j; i--){
                dp[i] = dp[i] | dp[i - j];
            }
            c -= g;
            g <<= 1;
        }
        int j = len * c;
        for (int i = subtree_size[node] - 1; i >= j; i--)
        {
            dp[i] = dp[i] | dp[i - j];
        }
    }
    int mx = 0;
    for (int i = 1; i < subtree_size[node]; i++){
        if(dp[i]){
            mx = max(mx, i * (subtree_size[node] - 1 - i));
        }
    }
    ans += mx;
}
 void solve()
{
    int n;
    cin >> n;
    t.resize(n + 1);
    subtree_size.assign(n + 1, 0);
    for (int i = 2; i <= n; i++)
    {
        int p;
        cin >> p;
        t[p].push_back(i);
    }
    dfs(1);
    cout << ans << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}