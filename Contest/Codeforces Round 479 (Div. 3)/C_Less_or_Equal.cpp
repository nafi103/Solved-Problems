#include<bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#define int int64_t
using namespace std;
using namespace __gnu_pbds;
typedef tree<int, null_type, less_equal<int>, rb_tree_tag, tree_order_statistics_node_update> PBDS;
/*define short pair*/
#define fs first
#define sc second
#define mkp make_pair
#define pb push_back
#define lb lower_bound
#define ub upper_bound
#define nl '\n'
#define all(x) x.begin(), x.end()
#define rall(a) (a).rbegin(),(a).rend()
 /*Array size declare */
const size_t sz = 1e6+123;
const size_t ss = 1e5+123;
 /*define iteration*/
#define ed end()
#define bg begin()
 /*datatype*/
#define ll long long
typedef unsigned long long ull;
typedef long double lld;
 /*math*/
#define eps 1e-15;
#define PI acos(-1);
const ll mod = 1e9 + 7;
const ll linf = (ll)1e17;
ll gcd(ll a, ll b){return b == 0 ? a : gcd(b, a % b);}
ll lcm ( ll a, ll b ) { return a * ( b / gcd ( a, b ) );}
 /*container declare */
typedef vector<ll> ve ;
typedef vector<ve> vve;
typedef pair<double, double> pdd;
typedef pair<ll, ll> pll;
typedef vector<pll> vll;
typedef map<ll,ll> mll;
typedef map<string,ll> msl;
typedef map<ll,ve> mlv;
typedef map<string,ve> msv;
 /*read ,Write of vector*/
#define read(v) for (auto &x : v) cin >> x;
#define write(v) for (auto &x : v) cout << x << " "; cout<<'\n';
#define rd1(a) cin >> a;
#define rd2(a,b) cin >> a >> b;
#define rd3(a,b,c) cin >> a >> b >> c;
#define rd4(a,b,c,d) cin >> a >> b >> c >> d;
#define p1(x) cout << x << ' ';
#define p2(x,y) cout << x << ' ' << y;
#define p3(x,y,z) cout << x << ' ' << y << z;
#define pn1(x) cout << x << '\n';
#define pn2(x,y) cout << x << ' ' << y << '\n';
#define pn3(x,y,z) cout << x << ' ' << y << ' ' << z << '\n';
 /*function - bitmask*/
#define lsb(x) ((x) & (-x))
#define nsz(t) __lg(t);
#define isp2(t) i && (i & -i) == i;
#define set_bits(x) __builtin_popcount(x)
 /*return value*/
#define sz(x) (ll)x.size()
 /*short printer*/
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
 /*Loop definaton*/
#define in(a, v) memset(a, v, sizeof(a));
#define f(i, a, b) for (int i = (a); i < (b); ++i)
#define r(i, a, b) for (int i = (a); i >= (b); --i)
 /*work faster*/
#define int ll
#define tif(condition) cout << ((condition) ? "YES\n" : "NO\n")
#define fraction() cout.unsetf(ios::floatfield); cout.precision(10); cout.setf(ios::fixed,ios::floatfield);
#define _   ios_base::sync_with_stdio(0); cin.tie(0);  cout.tie(0); char buffer[256];
 /***********Debugger**************/
#ifndef ONLINE_JUDGE
#define debug(x) cerr << #x <<": "; _print(x); cerr << endl;
#else
#define debug(x)
#endif
int prr[sz];
void pre(){
    in(prr,0);
 }
void solution();
int32_t main(){
    _
    ll tc=1;
    // rd1(tc);
    pre();
    f(i,1,tc+1){
        // p3("Case ",i,": ");
        solution();
   }
    return 0;  
}
void solution(){
    int n,k;
    cin >> n >> k;
    ve arr(n,k);
    read(arr);
    int cnt = 0;
    auto fun = [&](int val){
        cnt = 0;
        for(auto &ele : arr){
            if(ele <= val){
                cnt++;
            }
        }
        return cnt >= k;
    };
    int l = 1, r = 1e10;
    int ans = -1;
    while(l<=r){
        int mid = (l+r)/2;
        if(fun(mid)){
            ans = mid;
            r = mid-1;
        }else{
            l = mid + 1;
        }
    }
    fun(ans);
    if (cnt == k)
    {
        cout << ans << endl;
    }
    else
    {
        cout << -1 << endl;
    }
}   