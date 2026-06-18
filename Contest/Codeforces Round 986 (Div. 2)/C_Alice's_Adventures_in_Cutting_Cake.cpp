#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
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
template <class T> using pbds = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/


void solve()
{
    int n,m,taste,ans = 0;
    cin>>n>>m>>taste;
    vector<int>pref,suff,cake(n+1),pref_sum(n+1);
    pref.pb(0);suff.pb(0);pref_sum[0] = 0;
    for(int i = 1; i<=n; i++){
        cin>>cake[i];
        pref_sum[i] = pref_sum[i-1]+cake[i];
    }
    int curr_taste = 0;
    for(int i = 1; i<=n; i++){
        curr_taste+=cake[i];
        if(curr_taste>=taste){
            pref.pb(pref.back()+1);
            curr_taste = 0;
        }else{
            pref.pb(pref.back());
        }
    }
    curr_taste = 0;
    for(int i = n; i>=1; i--){
        curr_taste+=cake[i];
        if(curr_taste>=taste){
            suff.pb(suff.back()+1);
            curr_taste = 0;
        }else{
            suff.pb(suff.back());
        }
    }
    if(pref[n]<m and suff[n]<m){
        cout<<-1<<endl;
        return;
    }
    for(int i = 1; i<=n; i++){
        int need = m-pref[i-1];
        if(need<=0){
            ans = max(ans,pref_sum[n]-pref_sum[i-1]);
            break;
        }
        int pos = lower_bound(all(suff),need) - suff.begin();
        pos =  n - pos;
        if(i<=pos){
            ans = max(ans, pref_sum[pos] - pref_sum[i-1]);
        }
    }
    cout<<ans<<endl;
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
        // google(z);
        solve();
    }
}