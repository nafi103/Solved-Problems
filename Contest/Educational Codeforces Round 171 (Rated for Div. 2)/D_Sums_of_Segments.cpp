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
vector<int>v,start = {0,1},pref_sum,total_pref,contribution;

void resizeAll(int n){
    v.resize(n+1);
    pref_sum.resize(n+1);
    total_pref.resize(n+1);
    contribution.resize(n+1);
}

int get_partial(int i, int l, int r){
    if(r<l) return 0ll;
    return total_pref[r] - total_pref[l-1] - (r-l+1)*pref_sum[i-1];
}

void solve()
{
    int n;
    cin>>n;
    resizeAll(n);
    pref_sum[0] = 0; total_pref[0] = 0;
    for(int i = 1; i<=n; i++) {
        cin>>v[i];
        pref_sum[i] = pref_sum[i-1]+v[i];
        total_pref[i] = total_pref[i-1]+pref_sum[i];
    }
    debug(total_pref)
    contribution[n] = v[n];
    for(int i = n-1; i>=1; i--){
        contribution[i] = contribution[i+1] + (n-i+1)*v[i];
        start.pb(start.back()+i+1);
    }
    for(int i = 2; i<=n; i++){
        contribution[i]+=contribution[i-1];
    }
    int l,r,q;
    cin>>q;
    debug(start)
    while(q--){
        cin>>l>>r;
        int start_idx_l = upper_bound(all(start),l) - start.begin() - 1;
        int start_idx_r = upper_bound(all(start), r) - start.begin() - 1;
        debug(start_idx_l) debug(start_idx_r)
        int ll = l - start[start_idx_l] + start_idx_l, lr = n;
        int rl = start_idx_r, rr = r - start[start_idx_r] + start_idx_r;
        debug(ll) debug(lr) debug(rl) debug(rr)
        if(start_idx_r==start_idx_l){
            cout<<get_partial(start_idx_l, ll, rr)<<endl;
            continue;
        }
        int ans = contribution[start_idx_r-1] - contribution[start_idx_l];
        ans+=get_partial(start_idx_l,ll,lr);
        debug(get_partial(start_idx_l,ll,lr))
        ans+=get_partial(start_idx_r,rl,rr);
        cout<<ans<<endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}