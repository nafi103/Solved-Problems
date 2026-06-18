#include <bits/stdc++.h>
using namespace std;
 #define ll long long
#define mod 1000000007
#define pb push_back
#define fi first
#define se second
#define inf 0x3f3f3f3f
#define MAXN 100005
#define all(x) x.begin(), x.end()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rev(i, a, b) for (int i = (a); i >= (b); --i)
#define debug(x) cerr << #x << ": " << x << '\n'
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
#define read(x) cin >> x
#define write(x) cout << x << '\n'
#define readv(v)      \
    for (auto &x : v) \
    read(x)
#define writev(v)     \
    for (auto &x : v) \
    write(x)
#define endl "\n"
#define yes cout << "YES" << endl
#define no cout << "NO" << endl
 void solve()
{
    int n;
    cin >> n;
    int arr[2][n];
    int m = 2 * n, l = 2 * n - 1;
    for (int i = 0; i < n; i += 2)
    {
        arr[0][i] = m;
        m -= 2;
    }
    for (int i = n - 1; i >= 1; i -= 2)
    {
        arr[1][i] = l;
        l -= 2;
    }
    int k = 1;
    for (int i = 0; i < n; i += 2)
    {
        arr[1][i] = k;
        k++;
        if (i + 1 > n - 1)
            break;
        arr[0][i + 1] = k;
        k++;
    }
    for (int i = 0; i < 2; i++)
    {
        for (int j = 0; j < n; j++)
        {
            cout << arr[i][j] << " ";
        }
        cout << endl;
    }
}
 int main()
{
    fastIO;
    int t;
    cin >> t;
    while (t--)
        solve();
}