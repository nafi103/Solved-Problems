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
int n,a[100],b[100],dp[100][20002],pref[100],sqsum[100];

int f(int i, int sum){
    if(i==n)
        return 0;
    int &ans = dp[i][sum];
    if(ans!=-1)
        return ans;
    int &x = a[i], &y = b[i];
    ans = sqsum[i] + 2*(x*sum + y*((i?pref[i-1]:0)-sum)) + f(i+1,sum+x);
    swap(x,y);
    ans = min(ans,sqsum[i] + 2*(x*sum + y*((i?pref[i-1]:0)-sum)) + f(i+1,sum+x));
    return ans;
}

void solve()
{
    int mx = 0;
    cin>>n;
    for(int i = 0; i<n; i++){
        cin>>a[i];
    }
    for(int i = 0; i<n; i++){
        cin>>b[i];
        mx += max(a[i],b[i]);
        sqsum[i] = (a[i]*a[i] + b[i]*b[i])*(n-1);
        pref[i] = a[i]+b[i];
        if(i)
            pref[i]+=pref[i-1];
    }
    if(n==1){
        cout<<0<<endl;
        return;
    }
    for(int i = 0; i<n; i++){
        for(int j = 0; j<=mx; j++)
            dp[i][j] = -1;
    }
    cout<<f(0,0)<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}