#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define ld long double
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

const ld eps = 1e-15;

void solve()
{
    ld h,c,t;
    cin>>h>>c>>t;
    if(t==h){
        cout<<1<<endl;
        return;
    }else if(t<=(h+c)/2){
        cout<<2<<endl;
        return;
    }
    int l = 1, r = 1e15, k=-1;
    while(l<=r){
        int mid = (l+r)/2;
        int cold = mid, hot = mid+1;
        ld avg = (ld)((h*hot)+(c*cold))/(2*mid + 1);
        if(t-avg<eps){
            l = mid+1;
        }else{
            r = mid-1;
        }
    }
    if(eps<abs(t-((ld)((h*(r+1))+(c*r))/(2*r + 1)))-abs(t-((ld)((h*(l+1))+(c*l))/(2*l + 1)))){
        cout<<2*l+1<<endl;
    }else{
        cout<<2*r+1<<endl;
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