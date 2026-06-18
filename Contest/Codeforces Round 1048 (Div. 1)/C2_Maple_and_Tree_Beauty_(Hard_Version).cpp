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
int n;
 void dfs(int node, int l, vector<vector<int>> &t, vector<int>&level, vector<int> &cnt){
    level[node] = l;
    if(l>=sz(cnt)){
        cnt.push_back(1);
    }else{
        cnt[l]++;
    }
    for(auto &child: t[node]){
        dfs(child, l + 1, t, level, cnt);
    }
}
 void get_ans_100(int z, vector<int> &v){
    int total = accumulate(all(v), 0ll);
    bitset<100> b;
    b[0] = 1;
    for(auto &x: v){
        b = (b << x) | b;
    }
    for (int i = z; i >= 0; i--){
        if(b[i]==1){
            if(total-i<=n-z){
                cout << sz(v) << endl;
                return;
            }
        }
    }
    cout << sz(v) - 1 << endl;
}
 void get_ans_1000(int z, vector<int> &v)
{
    int total = accumulate(all(v), 0ll);
    bitset<1000> b;
    b[0] = 1;
    for (auto &x : v)
    {
        b = (b << x) | b;
    }
    for (int i = z; i >= 0; i--)
    {
        if (b[i] == 1)
        {
            if (total - i <= n - z)
            {
                cout << sz(v) << endl;
                return;
            }
        }
    }
    cout << sz(v) - 1 << endl;
}
 void get_ans_10000(int z, vector<int> &v)
{
    int total = accumulate(all(v), 0ll);
    bitset<10000> b;
    b[0] = 1;
    for (auto &x : v)
    {
        b = (b << x) | b;
    }
    for (int i = z; i >= 0; i--)
    {
        if (b[i] == 1)
        {
            if (total - i <= n - z)
            {
                cout << sz(v) << endl;
                return;
            }
        }
    }
    cout << sz(v) - 1 << endl;
}
 void get_ans_100010(int z, vector<int> &v)
{
    int total = accumulate(all(v), 0ll);
    bitset<100010> b;
    b[0] = 1;
    for (auto &x : v)
    {
        b = (b << x) | b;
    }
    for (int i = z; i >= 0; i--)
    {
        if (b[i] == 1)
        {
            if (total - i <= n - z)
            {
                cout << sz(v) << endl;
                return;
            }
        }
    }
    cout << sz(v) - 1 << endl;
}
 void solve()
{
    int z, final_level = inf;
    cin >> n >> z;
    vector<vector<int>> t(n+1);
    for (int i = 2; i <= n; i++){
        int p;
        cin >> p;
        t[p].push_back(i);
    }
    vector<int> level(n+1), count;
    dfs(1, 0, t, level, count);
    if(z>n-z)
        z = n - z;
    vector<int> v;
    for (int i = 1; i <= n; i++){
        if(t[i].empty())
            final_level = min(final_level, level[i]);
    }
    while(sz(count)>final_level+1)
        count.pop_back();
    if(z<100)
        get_ans_100(z, count);
    else if (z < 1000)
        get_ans_1000(z, count);
    else if (z < 1000)
        get_ans_10000(z, count);
    else
        get_ans_100010(z, count);
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}