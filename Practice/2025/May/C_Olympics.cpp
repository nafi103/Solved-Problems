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
const double EPS = 1e-12;
double a,b;

bool check(double mult){
    double ap = a*mult, bp = b*mult;
    double r = sqrt(ap*ap +  bp*bp) / 2;
    double rad = pi-(2.0*atan(ap/bp));
    double perimeter = 2.0*ap + 2.0*r*rad;
    return perimeter-400.0 > EPS;
}

double bs(double l, double r){
    if(abs(r-l)<EPS)
        return r;
    double mid = (l+r)/2.0;
    if(check(mid))
        return bs(l,mid-EPS);
    else
        return bs(mid+EPS,r);
}

void solve()
{
    char tmp;
    cin>>a>>tmp>>b;
    double mult = bs(EPS, 1000);
    cout<<a*mult<<" "<<b*mult<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}