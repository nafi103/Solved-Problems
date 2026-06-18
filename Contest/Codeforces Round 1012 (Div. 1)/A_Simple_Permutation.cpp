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

const int N = 1e5+10;
bool prime[N];

void solve()
{
    int n;
    cin>>n;
    int candidate, diff = inf;
    for(int i = 2; i<=n; i++){
        if(prime[i]){
            int left = i-1, right = n-i;
            if(diff>=abs(right-left)){
                diff = abs(right-left);
                candidate = i;
            }
        }
    }
    int l = candidate-1, r = candidate+1;
    cout<<candidate<<" ";
    for(int i = 1; i<n; i++){
        if(l>0 and ((i&1) or r>n)){
            cout<<l--<<" ";
        }else{
            cout<<r++<<" ";
        }
    }
    cout<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    memset(prime,1,sizeof prime);
    prime[1] = false;
    for(int i = 2; i*i<N; i++){
        if(prime[i]){
            for(int j = i*i; j<N; j+=i)
                prime[j] = false;
        }
    }
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}