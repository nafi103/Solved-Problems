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
    int n,x;
    cin>>n;
    vector<pair<int,int>>a(n),b(n);
    for(int i = 0; i<n; i++){
        cin>>x;
        a[i].ff = x;
        a[i].ss = i;
    }
    for(int i = 0; i<n; i++){
        cin>>x;
        b[i].ff = x;
        b[i].ss = i;
    }
    sort(all(a));
    sort(all(b));
    int opa = 0, opb = 0;
    bool flag = false;
    pbds<int>d1,d2;
    for(int i = 0; i<n; i++){
        if(a[i].ff!=b[i].ff){
            no;
            return;
        }
        if(i and a[i].ff==a[i-1].ff)
            flag = true;
        int after_curr_a = sz(d1) - d1.order_of_key(a[i].ss);
        int after_curr_b = sz(d2) - d2.order_of_key(b[i].ss);
        opa+=max(0ll,a[i].ss+after_curr_a - i);
        opb+=max(0ll,b[i].ss+after_curr_b - i);
        d1.insert(a[i].ss);
        d2.insert(b[i].ss);
    }
    if(flag or abs(opa-opb)%2==0){
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