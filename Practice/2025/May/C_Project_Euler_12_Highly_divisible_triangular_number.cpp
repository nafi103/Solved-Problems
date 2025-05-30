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
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
vector<int>ans(1030,0);


void solve()
{
    int n;
    cin>>n;
    cout<<ans[n]<<endl;
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
    int sum = 1,mx_div = 0;
    for(int i = 2;i<=41040; i++){
        sum+=i;
        int tmp = sum,divisor = 1;
        for(int i = 2; i*i<=tmp; i++){
            int cnt = 0;
            while(tmp%i==0){
                cnt++;
                tmp/=i;
            }
            divisor*=(cnt+1);
        }
        if(tmp>1)
            divisor*=2;
        if(divisor<1030 and ans[divisor-1]==0){
            ans[divisor-1] = sum;
        }
    }
    for(int i = 1023; i>=1; i--){
        if(ans[i]==0)
            ans[i] = ans[i+1];
    }
    for(int i = 1022; i>=1; i--){
        ans[i] = min(ans[i+1],ans[i]);
    }
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}