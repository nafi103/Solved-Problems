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


void solve()
{
    int n;
    cin>>n;
    using pii = pair<int,int>;
    vector<pii>p(n);
    for(int i = 0; i<n; i++){
        cin>>p[i].ff;
        p[i].ss = i;
    }
    if(n<=2){
        yes;
        return;
    }
    sort(all(p));
    multiset<int>s,mx;
    if((p[0].ss==0 and p[1].ss==n-1) or (p[0].ss==n-1 and p[1].ss==0)){
        s.insert(0);
        s.insert(n-1);
        mx.insert(n-2);
        for(int i = 2; i<n; i++){
            s.insert(p[i].ss);
            // debug(mx);
            // debug(s);
            int left = *(prev(s.lower_bound(p[i].ss)));
            int right = *s.upper_bound(p[i].ss);
            int right_faka = right - p[i].ss - 1;
            int left_faka = p[i].ss - left - 1;
            // debug(left) debug(right)
            // debug(left_faka) debug(right_faka)
            if(min(left_faka,right_faka)!=((*mx.rbegin())-1)/2){
                no;
                return;
            }
            mx.erase(mx.lower_bound(right - left - 1));
            mx.insert(left_faka); mx.insert(right_faka);
        }
        yes;
    }else{
        no;
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}