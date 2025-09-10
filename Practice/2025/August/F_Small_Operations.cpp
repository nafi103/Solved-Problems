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
const int N = 1e6+10;
int k;
vector<int> max_prime(N), dp(N);

int f(int z){
    if(z==1)
        return 0;
    int &ans = dp[z];
    if(ans!=-1)
        return dp[z];
    ans = inf;
    for(int i = 2; i*i<=z; i++){
        if(z%i==0){
            int t = z/i;
            if(t<=k)
                ans = min(ans,1+f(z/t));
            if(i<=k)
                ans = min(ans,1+f(z/i));
        }
    }
    return ans;
}

void solve()
{
    int x,y, mx = 0;
    cin>>x>>y>>k;
    mx = max(x+1,y+1);
    for(int i = 2; i<mx; i++)
        dp[i] = (i<=k?1:-1);
    
    if(x==y){
        cout<<0<<endl;
        return;
    }
    int g = gcd(x,y);
    x/=g;y/=g;
    if(max_prime[x]>k or max_prime[y]>k){
        cout<<-1<<endl;
        return;
    }
    cout<<f(x)+f(y)<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    dp[1] = 0;
    iota(all(max_prime),0);
    for(int i = 2; i<N; i++){
        if(max_prime[i]==i){
            for(int j = i+i; j<N; j+=i){
                max_prime[j] = i;
            }
        }
    }
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}