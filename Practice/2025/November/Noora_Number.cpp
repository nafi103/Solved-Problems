#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
int dp[20][2048];

int n;
vector<int> num;

void process(int x)
{
    num.clear();
    while (x > 0)
    {
        num.push_back(x % 10);
        x /= 10;
    }
    n = sz(num);
}

int f(int pos, int mask, int flag){
    if(pos==-1){
        return (__builtin_popcount(mask) == (31 - __builtin_clz(mask)) && mask);
    }
    int ans = dp[pos][mask];
    if(ans != -1 and flag){
        return ans;
    }
    ans = 0;
    int r = (flag ? 9 : num[pos]);
    for (int i = r; i >= 0; i--){
        int new_flag = (i == r ? flag : 1);
        int new_mask = mask;
        if(!(mask==0 and i==0))
            new_mask |= (1 << i);
        ans += f(pos - 1, new_mask, new_flag);
    }
    if(flag)
        dp[pos][mask] = ans;
    return ans;
}

void solve()
{
    cin>>n;
    if(n==1){
        cout << 1 << endl;
        return;
    }
    process(n);
    cout << f(n-1, 0, 0) << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    memset(dp, -1, sizeof dp);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}