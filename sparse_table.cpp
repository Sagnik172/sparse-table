#include<bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp> 
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
using namespace __gnu_pbds;
#define fastio() ios_base::sync_with_stdio(false);cin.tie(NULL);cout.tie(NULL)
#define MOD 1000000007
#define MOD1 998244353
#define MAXN   1000001
#define INF 1e18
#define nline "\n"
#define pb push_back
#define ppb pop_back
#define mp make_pair
#define ff first
#define ss second
#define PI 3.141592653589793238462
#define set_bits __builtin_popcountll
#define sz(x) ((int)(x).size())
#define all(x) (x).begin(), (x).end()
#define f(i,a,b) for(long long i=a;i<=b;i++)
#define fr(i,a,b) for(long long i=a;i>=b;i--)
#define ain(a,n) for(ll i=0;i<n;i++)cin>>(a)[i]
#define vll vector<ll>
#define show(a) for(auto x:a)cout<<x<<" ";
#pragma GCC optimize("O3,unroll-loops")
#pragma GCC target("avx2,bmi,bmi2,lzcnt,popcnt")
int spf[MAXN];
typedef long long ll;
typedef unsigned long long ull;
typedef long double lld;
// typedef tree<pair<int, int>, null_type, less<pair<int, int>>, rb_tree_tag, tree_order_statistics_node_update > pbds; // find_by_order, order_of_key
#define ordered_set tree<int, null_type,less<int>, rb_tree_tag,tree_order_statistics_node_update>
// order_of_key (k) : Number of items strictly smaller than k .
// find_by_order(k) : K-th element in a set (counting from zero).
#ifndef ONLINE_JUDGE
#define debug(x) cerr << #x <<" "; _print(x); cerr << endl;
#else
#define debug(x)
#endif
 
void _print(ll t) {cerr << t;}
void _print(int t) {cerr << t;}
void _print(string t) {cerr << t;}
void _print(char t) {cerr << t;}
void _print(lld t) {cerr << t;}
void _print(double t) {cerr << t;}
void _print(ull t) {cerr << t;}
 
template <class T, class V> void _print(pair <T, V> p);
template <class T> void _print(vector <T> v);
template <class T> void _print(set <T> v);
template <class T, class V> void _print(map <T, V> v);
template <class T> void _print(multiset <T> v);
template <class T, class V> void _print(pair <T, V> p) {cerr << "{"; _print(p.ff); cerr << ","; _print(p.ss); cerr << "}";}
template <class T> void _print(vector <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(set <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T> void _print(multiset <T> v) {cerr << "[ "; for (T i : v) {_print(i); cerr << " ";} cerr << "]";}
template <class T, class V> void _print(map <T, V> v) {cerr << "[ "; for (auto i : v) {_print(i); cerr << " ";} cerr << "]";}
#define N 50005
ll lis(vector<ll> const& a) {
    ll n = a.size();
    
    vector<ll> d(n+1, INF);
    d[0] = -INF;

    for (ll i = 0; i < n; i++) {
        ll j = upper_bound(d.begin(), d.end(), a[i]) - d.begin();
        if (d[j-1] <= a[i] && a[i] <= d[j])
            d[j] = a[i];
    }

    ll ans = 0;
    for (ll i = 0; i <= n; i++) {
        if (d[i] < INF)
            ans = i;
    }
    return ans;
}
vector<ll> sieve(ll n)
{
    ll *arr = new ll[n + 1]();
    vector<ll> vect;
    for (ll i = 2; i <= n; i++)
        if (arr[i] == 0)
        {
            vect.push_back(i);
            for (ll j = (i * i); j <= n; j += i)
                arr[j] = 1;
        }
    return vect;
}
void sieve()
{
    spf[1] = 1;
    for (int i=2; i<MAXN; i++)
        spf[i] = i;
    for (int i=4; i<MAXN; i+=2)
        spf[i] = 2;
 
    for (int i=3; i*i<MAXN; i++)
    {
        if (spf[i] == i)
        {
            for (int j=i*i; j<MAXN; j+=i)
                if (spf[j]==j)
                    spf[j] = i;
        }
    }
}
map<ll,ll> getFactm(ll x)
{
    map<ll,ll> ret;
    while (x!=1)
    {
        ret[spf[x]]++;
        x=x/spf[x];
    }
    return ret;
}
ll expo(ll a, ll b, ll mod)
{
    ll res = 1;
    while (b > 0)
    {
        if (b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b = b >> 1;
    }
    return res;
}
ll mminvprime(ll a, ll b) { return expo(a, b - 2, b); }
ll mod_inv(ll a, ll mod){
    return expo(a,mod-2,mod);
} 
ll mod_add(ll a, ll b, ll m)
{
    a = a % m;
    b = b % m;
    return (((a + b) % m) + m) % m;
}
ll mod_mul(ll a, ll b, ll m)
{
    a = a % m;
    b = b % m;
    return (((a * b) % m) + m) % m;
}
ll mod_sub(ll a, ll b, ll m)
{
    a = a % m;
    b = b % m;
    return (((a - b) % m) + m) % m;
}
ll mod_div(ll a, ll b, ll m)
{
    a = a % m;
    b = b % m;
    return (mod_mul(a, mminvprime(b, m), m) + m) % m;
}
void google(ll t) { cout << "Case #" << t << ": "; }
ll nCrFermat(ll n, ll r,ll fact[], ll mod){
    if(n<r || r < 0) return 0;
    if(n == r)
        return 1;

    if(r==0) return 1;
    return mod_mul((ll)fact[n] , mod_mul(mod_inv((ll)fact[n-r],mod) , mod_inv((ll)fact[r],mod) , mod) , mod);
    return (fact[n]*((mod_inv(fact[n-r],mod)*mod_inv(fact[r],mod))%mod))%mod;
} 
void init_code(){
    fastio();
    #ifndef ONLINE_JUDGE
    freopen("input.txt", "r", stdin);
    freopen("output.txt", "w", stdout);
    #endif 
}
/*
------SPARSE TABLE----
range gcd,max,min in o(1)
others in o(log n)
doesn't support update queries
*/
class SP_table{
public:
    function<ll(ll,ll)> fun;
    vector<vll> st;
    vll floorlog;
    ll n;
    SP_table(ll size,vll &a,function<ll(ll,ll)> fun1):fun(fun1),n(size)
    {
        st.assign(size+1,vll(32,0));
        floorlog.assign(size+1,0ll);
        f(i,0,size-1)
        st[i][0]=a[i];

        f(i,1,31)
        {
            f(j,0,size-1)
            {
                if(j+(1ll<<(i-1))<size)
                st[j][i]=fun(st[j][i-1],st[j+(1ll<<(i-1))][i-1]);
            }
        }
        for(ll i=0;(1ll<<i)<=size;i++)
        {
            for(ll j=(1<<i);j<=size && j<(1<<(i+1)); j++)
                floorlog[j]=i;
        }
    }
    //for non-idempotent funx\ctions
    ll query(ll l,ll r,ll init)
    {
        ll ans=init;
        fr(i,31,0)
        {
            if(l+(1ll<<i)-1<=r)
            {
                ans=fun(ans,st[l][i]);
                l+=(1ll<<i);
            }
        }
        return ans;
    }
    //for idempotent funcs.eg:-gcd,min,max
    ll rmq(ll l,ll r)
    {
        ll k=floorlog[r-l+1];
        return fun(st[l][k],st[r-(1ll<<k)+1][k]);
    }



};
void solve()
{
    ll n=5;
    vll a={1,2,3,4,5};
    SP_table sp(n,a,[&](ll a,ll b){return min(a,b);});
    cout<<sp.rmq(2,4);

    

        
}
 
 
int main() {
#ifndef ONLINE_JUDGE
   freopen("Error.txt", "w", stderr);
#endif
   init_code();
   // ll t;
   // cin>>t;
   // while(t--)
   
     solve();
   
return 0;
  
 
    


}
